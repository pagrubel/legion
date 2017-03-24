-- Copyright 2017 Stanford University
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

import "regent"

local c = regentlib.c

stream_array_size = 100000000
num_tasks = 2
num_iterations = 100

fspace triple {
  a : double,
  b : double,
  c : double 
}

task triad(a : region(ispace(int1d), triple), scalar:double, id:int)
where reads writes(a) do
  for i = 0, num_iterations do
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
  c.printf("Running triad with %d iterations, %d tasks, and an %ld Mbyte array\n", 
    num_iterations, num_tasks, [ sizeof(triple) ] * (stream_array_size / 1e6))
  var a = region(ispace(int1d, stream_array_size), triple)
  fill(a, {0.0, 1.0, 2.0})
  var p = partition(equal, a, ispace(int1d, num_tasks))
  var starttime = timer(a)
  for i in p.colors do
    triad(p[i], 3.0, i)
  end
  var endtime = timer(a)
  var elapsed : double = endtime-starttime

  c.printf("MB/S = %f\n", (1.0 * [ sizeof(triple) ] * stream_array_size * num_iterations) / elapsed)
end

-- main:getast():printpretty(true)
regentlib.start(main)
