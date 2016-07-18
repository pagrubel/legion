-- Copyright 2016 Stanford University
--
-- Licensed under the Apache License, Version 2.0 (the "License");
-- you may not use this file except in compliance with the License.
-- You may obtain a copy of the License at
--
--     http://www.apache.org/licenses/LICENSE-2.0
--
-- Unless required by applicable law or agreed to in writing, software
-- distributed under the License is distributed on an "AS IS" BASIS,
-- WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
-- See the License for the specific language governing permissions and
-- limitations under the License.

-- Inspired by https://github.com/ParRes/Kernels/tree/master/LEGION/Stencil

import "regent"

local DTYPE = double
local RADIUS = 2
local USE_FOREIGN = true

local c = regentlib.c

-- Compile and link stencil.cc
if USE_FOREIGN then
  local root_dir = arg[0]:match(".*/") or "./"
  local stencil_cc = root_dir .. "stencil.cc"
  if os.getenv('SAVEOBJ') == '1' then
    stencil_so = root_dir .. "libstencil.so"
  else
    stencil_so = os.tmpname() .. ".so" -- root_dir .. "stencil.so"
  end
  local cxx = os.getenv('CXX') or 'c++'

  local cxx_flags = "-O3 -Wall -Werror -DDTYPE=" .. tostring(DTYPE) .. " -DRESTRICT=__restrict__ -DRADIUS=" .. tostring(RADIUS)
  if os.execute('test "$(uname)" = Darwin') == 0 then
    cxx_flags =
      (cxx_flags ..
         " -dynamiclib -single_module -undefined dynamic_lookup -fPIC")
  else
    cxx_flags = cxx_flags .. " -shared -fPIC"
  end

  local cmd = (cxx .. " " .. cxx_flags .. " " .. stencil_cc .. " -o " .. stencil_so)
  if os.execute(cmd) ~= 0 then
    print("Error: failed to compile " .. stencil_cc)
    assert(false)
  end
  terralib.linklibrary(stencil_so)
  cstencil = terralib.includec("stencil.h", {"-I", root_dir,
                              "-DDTYPE=" .. tostring(DTYPE),
                              "-DRESTRICT=__restrict__",
                              "-DRADIUS=" .. tostring(RADIUS)})
end

local min = regentlib.fmin
local max = regentlib.fmax

fspace point {
  input : DTYPE,
  output : DTYPE,
}

terra to_rect(lo : int2d, hi : int2d) : c.legion_rect_2d_t
  return c.legion_rect_2d_t {
    lo = lo:to_point(),
    hi = hi:to_point(),
  }
end

task make_tile_partition(points : region(ispace(int2d), point),
                         tiles : ispace(int1d),
                         n : int64, nt : int64, radius : int64)
  var coloring = c.legion_domain_point_coloring_create()
  var npoints = n + 2*nt*radius
  for ix = 0, nt do
    for iy = 0, nt do
      var i = int1d(iy*nt + ix)
      var lo = int2d { x = ix*npoints/nt, y = iy*npoints/nt }
      var hi = int2d { x = (ix+1)*npoints/nt - 1, y = (iy+1)*npoints/nt - 1 }
      var rect = to_rect(lo, hi)
      c.legion_domain_point_coloring_color_domain(
        coloring, i:to_domain_point(), c.legion_domain_from_rect_2d(rect))
    end
  end
  var p = partition(disjoint, points, coloring, tiles)
  c.legion_domain_point_coloring_destroy(coloring)
  return p
end

task make_interior_partition(points : region(ispace(int2d), point),
                             tiles : ispace(int1d),
                             n : int64, nt : int64, radius : int64)
  var coloring = c.legion_domain_point_coloring_create()
  var npoints = n + 2*nt*radius
  for ix = 0, nt do
    for iy = 0, nt do
      var i = int1d(iy*nt + ix)
      var lo = int2d { x = ix*npoints/nt + radius, y = iy*npoints/nt + radius }
      var hi = int2d { x = (ix+1)*npoints/nt - 1 - radius, y = (iy+1)*npoints/nt - 1 - radius }
      var rect = to_rect(lo, hi)
      c.legion_domain_point_coloring_color_domain(
        coloring, i:to_domain_point(), c.legion_domain_from_rect_2d(rect))
    end
  end
  var p = partition(disjoint, points, coloring, tiles)
  c.legion_domain_point_coloring_destroy(coloring)
  return p
end

task make_exterior_partition(points : region(ispace(int2d), point),
                             tiles : ispace(int1d),
                             n : int64, nt : int64, radius : int64)
  var coloring = c.legion_domain_point_coloring_create()
  var npoints = n + 2*nt*radius
  for ix = 0, nt do
    for iy = 0, nt do
      var i = int1d(iy*nt + ix)

      var loffx, loffy = radius, radius
      if ix == 0 then loffx = 0 end
      if iy == 0 then loffy = 0 end

      var hoffx, hoffy = radius, radius
      if ix == nt - 1 then hoffx = 0 end
      if iy == nt - 1 then hoffy = 0 end

      var lo = int2d { x = ix*npoints/nt + loffx, y = iy*npoints/nt + loffy }
      var hi = int2d { x = (ix+1)*npoints/nt - 1 - hoffx, y = (iy+1)*npoints/nt - 1 - hoffy }
      var rect = to_rect(lo, hi)
      c.legion_domain_point_coloring_color_domain(
        coloring, i:to_domain_point(), c.legion_domain_from_rect_2d(rect))
    end
  end
  var p = partition(disjoint, points, coloring, tiles)
  c.legion_domain_point_coloring_destroy(coloring)
  return p
end

terra clamp(val : int64, lo : int64, hi : int64)
  return min(max(val, lo), hi)
end

task make_ghost_x_partition(points : region(ispace(int2d), point),
                            tiles : ispace(int1d),
                            n : int64, nt : int64, radius : int64, dir : int64)
  var coloring = c.legion_domain_point_coloring_create()
  for ix = 0, nt do
    for iy = 0, nt do
      var i = int1d(iy*nt + ix)

      var lo = int2d { x = clamp((ix+dir)*radius, 0, nt*radius), y = iy*n/nt }
      var hi = int2d { x = clamp((ix+1+dir)*radius - 1, -1, nt*radius - 1), y = (iy+1)*n/nt - 1 }
      var rect = to_rect(lo, hi)
      c.legion_domain_point_coloring_color_domain(
        coloring, i:to_domain_point(), c.legion_domain_from_rect_2d(rect))
    end
  end
  var p = partition(disjoint, points, coloring, tiles)
  c.legion_domain_point_coloring_destroy(coloring)
  return p
end

task make_ghost_y_partition(points : region(ispace(int2d), point),
                            tiles : ispace(int1d),
                            n : int64, nt : int64, radius : int64, dir : int64)
  var coloring = c.legion_domain_point_coloring_create()
  for ix = 0, nt do
    for iy = 0, nt do
      var i = int1d(iy*nt + ix)

      var lo = int2d { x = ix*n/nt, y = clamp((iy+dir)*radius, 0, nt*radius) }
      var hi = int2d { x = (ix+1)*n/nt - 1, y = clamp((iy+1+dir)*radius - 1, -1, nt*radius - 1) }
      var rect = to_rect(lo, hi)
      c.legion_domain_point_coloring_color_domain(
        coloring, i:to_domain_point(), c.legion_domain_from_rect_2d(rect))
    end
  end
  var p = partition(disjoint, points, coloring, tiles)
  c.legion_domain_point_coloring_destroy(coloring)
  return p
end

local function off(i, x, y)
  return rexpr int2d { x = i.x + x, y = i.y + y } end
end

local function make_stencil_pattern(points, index, off_x, off_y, radius)
  local value
  for i = 1, radius do
    local neg = off_x < 0 or off_y < 0
    local coeff = ((neg and -1) or 1)/(2*i*radius)
    local x, y = off_x*i, off_y*i
    local component = rexpr coeff*points[ [off(index, x, y)] ].input end
    if value then
      value = rexpr value + component end
    else
      value = rexpr component end
    end
  end
  return value
end

__demand(__inline)
task get_rect(is : ispace(int2d))
  return c.legion_domain_get_rect_2d(
    c.legion_index_space_get_domain(__runtime(), __raw(is)))
end

terra get_base_and_stride(rect : c.legion_rect_2d_t,
                          physical : c.legion_physical_region_t,
                          field : c.legion_field_id_t)
  var subrect : c.legion_rect_2d_t
  var offsets : c.legion_byte_offset_t[2]
  var accessor = c.legion_physical_region_get_field_accessor_generic(physical, field)
  var base_pointer = [&DTYPE](c.legion_accessor_generic_raw_rect_ptr_2d(
                                      accessor, rect, &subrect, &(offsets[0])))
  regentlib.assert(base_pointer ~= nil, "base pointer is nil")
  regentlib.assert(subrect.lo.x[0] == rect.lo.x[0] and subrect.lo.x[1] == rect.lo.x[1], "subrect not equal to rect")
  regentlib.assert(subrect.hi.x[0] == rect.hi.x[0] and subrect.hi.x[1] == rect.hi.x[1], "subrect not equal to rect")
  regentlib.assert(offsets[0].offset == terralib.sizeof(DTYPE), "stride does not match expected value")

  return { base = base_pointer, stride = offsets[1].offset }
end

local function make_stencil_interior(private, interior, radius)
  if not USE_FOREIGN then
    return rquote
      for i in interior do
        private[i].output = private[i].output +
          [make_stencil_pattern(private, i,  0, -1, radius)] +
          [make_stencil_pattern(private, i, -1,  0, radius)] +
          [make_stencil_pattern(private, i,  1,  0, radius)] +
          [make_stencil_pattern(private, i,  0,  1, radius)]
      end
    end
  else
    local weight
    __demand(__inline)
    task weight(i : int64, j : int64, radius : int64)
      return (j + radius)*(2*radius + 1) + (i + radius)
    end

    return rquote
      var rect = get_rect(private.ispace)
      var { base_input = base, stride_input = stride } = get_base_and_stride(rect, __physical(private)[0], __fields(private)[0])
      var { base_output = base, stride_output = stride } = get_base_and_stride(rect, __physical(private)[1], __fields(private)[1])
      regentlib.assert(stride_output == stride_input, "strides do not match")

      var weights : double[(2*radius + 1)*(2*radius + 1)]
      for i = -radius, radius + 1 do
        for j = -radius, radius + 1 do
          weights[weight(i, j, radius)] = 0
        end
      end
      for i = 1, radius + 1 do
        weights[weight( 0,  i, radius)] =  1.0/(2.0*i*radius)
        weights[weight( i,  0, radius)] =  1.0/(2.0*i*radius)
        weights[weight( 0, -i, radius)] = -1.0/(2.0*i*radius)
        weights[weight(-i,  0, radius)] = -1.0/(2.0*i*radius)
      end

      var interior_rect = get_rect(interior.ispace)
      cstencil.stencil(base_input, base_output, weights,
                       stride_input / [terralib.sizeof(DTYPE)],
                       interior_rect.lo.x[0] - rect.lo.x[0], interior_rect.hi.x[0] - rect.lo.x[0] + 1,
                       interior_rect.lo.x[1] - rect.lo.x[1], interior_rect.hi.x[1] - rect.lo.x[1] + 1)
    end
  end
end

local function make_stencil(radius)
  local task st(private : region(ispace(int2d), point),
                interior : region(ispace(int2d), point),
                xm : region(ispace(int2d), point),
                xp : region(ispace(int2d), point),
                ym : region(ispace(int2d), point),
                yp : region(ispace(int2d), point),
                print_ts : bool)
  where
    reads writes(private.{input, output}),
    reads(xm.input, xp.input, ym.input, yp.input)
  do
    if print_ts then c.printf("t: %ld\n", c.legion_get_current_time_in_micros()) end

    var interior_rect = get_rect(interior.ispace)
    var interior_lo = int2d { x = interior_rect.lo.x[0], y = interior_rect.lo.x[1] }
    var interior_hi = int2d { x = interior_rect.hi.x[0], y = interior_rect.hi.x[1] }
    var xm_rect = get_rect(xm.ispace)
    var xm_lo = int2d { x = xm_rect.lo.x[0], y = xm_rect.lo.x[1] }
    var xp_rect = get_rect(xp.ispace)
    var xp_lo = int2d { x = xp_rect.lo.x[0], y = xp_rect.lo.x[1] }
    var ym_rect = get_rect(ym.ispace)
    var ym_lo = int2d { x = ym_rect.lo.x[0], y = ym_rect.lo.x[1] }
    var yp_rect = get_rect(yp.ispace)
    var yp_lo = int2d { x = yp_rect.lo.x[0], y = yp_rect.lo.x[1] }

    for i in xm do
      var i2 = i - xm_lo + interior_lo + { -radius, 0 }
      private[i2].input = xm[i].input
    end
    for i in ym do
      var i2 = i - ym_lo + interior_lo + { 0, -radius }
      private[i2].input = ym[i].input
    end
    for i in xp do
      var i2 = i - xp_lo + { x = interior_hi.x + 1, y = interior_lo.y }
      private[i2].input = xp[i].input
    end
    for i in yp do
      var i2 = i - yp_lo + { x = interior_lo.x, y = interior_hi.y + 1 }
      private[i2].input = yp[i].input
    end

    [make_stencil_interior(private, interior, radius)]
  end
  return st
end
local stencil = make_stencil(RADIUS)

local function make_increment_interior(private, exterior)
  if not USE_FOREIGN then
    return rquote
      for i in exterior do
        private[i].input = private[i].input + 1
      end
    end
  else
    return rquote
      var rect = get_rect(private.ispace)
      var { base_input = base, stride_input = stride } = get_base_and_stride(rect, __physical(private)[0], __fields(private)[0])

      var exterior_rect = get_rect(exterior.ispace)
      cstencil.increment(base_input,
                         stride_input / [terralib.sizeof(DTYPE)],
                         exterior_rect.lo.x[0] - rect.lo.x[0], exterior_rect.hi.x[0] - rect.lo.x[0] + 1,
                         exterior_rect.lo.x[1] - rect.lo.x[1], exterior_rect.hi.x[1] - rect.lo.x[1] + 1)
    end
  end
end

task increment(private : region(ispace(int2d), point),
               exterior : region(ispace(int2d), point),
               xm : region(ispace(int2d), point),
               xp : region(ispace(int2d), point),
               ym : region(ispace(int2d), point),
               yp : region(ispace(int2d), point),
               print_ts : bool)
where reads writes(private.input, xm.input, xp.input, ym.input, yp.input) do
  [make_increment_interior(private, exterior)]
  for i in xm do i.input += 1 end
  for i in xp do i.input += 1 end
  for i in ym do i.input += 1 end
  for i in yp do i.input += 1 end

  if print_ts then c.printf("t: %ld\n", c.legion_get_current_time_in_micros()) end
end

task check(private : region(ispace(int2d), point),
           interior : region(ispace(int2d), point),
           tsteps : int64, init : int64)
where reads(private.{input, output}) do
  var expect_in = init + tsteps
  var expect_out = init
  for i in interior do
    if private[i].input ~= expect_in then
      for i2 in interior do
        c.printf("input (%lld,%lld): %.0f should be %lld\n",
                 i2.x, i2.y, private[i2].input, expect_in)
      end
    end
    regentlib.assert(private[i].input == expect_in, "test failed")
    if private[i].output ~= expect_out then
      for i2 in interior do
        c.printf("output (%lld,%lld): %.0f should be %lld\n",
                 i2.x, i2.y, private[i2].output, expect_out)
      end
    end
    regentlib.assert(private[i].output == expect_out, "test failed")
  end
end

task main()
  var nbloated : int64 = 12 -- Grid size along each dimension, including border.
  var nt : int64 = 4
  var tsteps : int64 = 10
  var init : int64 = 1000

  var radius : int64 = RADIUS
  var n : int64 = nbloated - 2*radius -- Grid size, minus the border.
  regentlib.assert(n >= nt, "grid too small")

  var grid = ispace(int2d, { x = n + 2*nt*radius, y = n + 2*nt*radius })
  var nt2 = nt*nt
  var tiles = ispace(int1d, nt2)

  var points = region(grid, point)
  var private = make_tile_partition(points, tiles, n, nt, radius)
  var interior = make_interior_partition(points, tiles, n, nt, radius)
  var exterior = make_exterior_partition(points, tiles, n, nt, radius)

  var xm = region(ispace(int2d, { x = nt*radius, y = n }), point)
  var xp = region(ispace(int2d, { x = nt*radius, y = n }), point)
  var ym = region(ispace(int2d, { x = n, y = nt*radius }), point)
  var yp = region(ispace(int2d, { x = n, y = nt*radius }), point)
  var pxm_in = make_ghost_x_partition(xm, tiles, n, nt, radius, -1)
  var pxp_in = make_ghost_x_partition(xp, tiles, n, nt, radius,  1)
  var pym_in = make_ghost_y_partition(ym, tiles, n, nt, radius, -1)
  var pyp_in = make_ghost_y_partition(yp, tiles, n, nt, radius,  1)
  var pxm_out = make_ghost_x_partition(xm, tiles, n, nt, radius, 0)
  var pxp_out = make_ghost_x_partition(xp, tiles, n, nt, radius, 0)
  var pym_out = make_ghost_y_partition(ym, tiles, n, nt, radius, 0)
  var pyp_out = make_ghost_y_partition(yp, tiles, n, nt, radius, 0)

  fill(points.{input, output}, init)
  fill(xm.{input, output}, init)
  fill(xp.{input, output}, init)
  fill(ym.{input, output}, init)
  fill(yp.{input, output}, init)

  __demand(__spmd)
  for t = 0, tsteps do
    -- __demand(__parallel)
    for i = 0, nt2 do
      stencil(private[i], interior[i], pxm_in[i], pxp_in[i], pym_in[i], pyp_in[i], t == 0)
    end
    -- __demand(__parallel)
    for i = 0, nt2 do
      increment(private[i], exterior[i], pxm_out[i], pxp_out[i], pym_out[i], pyp_out[i], t == tsteps - 1)
    end
  end

  for i = 0, nt2 do
    check(private[i], interior[i], tsteps, init)
  end
end
regentlib.start(main)