import "regent"

local c = regentlib.c
local cstr = terralib.includec("string.h")
local std = terralib.includec("stdlib.h")
fspace triple {
  a : double,
  b : double,
  c : double 
}

task triad(a : region(ispace(int1d), triple), scalar:double, id:int, num_it:int )
where reads writes(a) do
  for i = 0, num_it do
    for i in a do
      i.a = i.b + scalar * i.c
    end
  end
end

task timer(a : region(ispace(int1d), triple)) : int64
where reads writes(a) do
  return c.legion_get_current_time_in_micros()
end

task main()

  var stream_array_size = 1000000
  var num_tasks = 10
  var num_iterations = 100


  var args = c.legion_runtime_get_input_args()
  for i = 0, args.argc do
    if cstr.strcmp(args.argv[i], "-sas") == 0 then
      stream_array_size = std.atoi(args.argv[i + 1])
    elseif cstr.strcmp(args.argv[i], "-nt") == 0 then
      num_tasks = std.atoi(args.argv[i + 1])
    elseif cstr.strcmp(args.argv[i], "-ni") == 0 then
      num_iterations = std.atoi(args.argv[i + 1])
    end
  end
--
  c.printf("Running triad with %d iterations, %d tasks, and a %ld MB array\n", 
    num_iterations, num_tasks, [ sizeof(triple) ] * (stream_array_size / 1e6))
  var a = region(ispace(int1d, stream_array_size), triple)
  fill(a, {0.0, 1.0, 2.0})
  var p = partition(equal, a, ispace(int1d, num_tasks))
  var starttime = timer(a)
  for i in p.colors do
    triad(p[i], 3.0, i, num_iterations)
  end
  var endtime = timer(a)
  var elapsed : double = endtime-starttime

  c.printf("MB/S = %f\n", (1.0 * [ sizeof(triple) ] * stream_array_size * num_iterations) / elapsed)
end

regentlib.start(main)
