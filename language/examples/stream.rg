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
  c.printf("Running triad with %d iterations, %d tasks, and a %ld MB array\n", 
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

regentlib.start(main)
