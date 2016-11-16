/* Copyright 2016 Stanford University
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */


#include <cstdio>
#include <cassert>
#include <cstdlib>
#include "legion.h"
using namespace Legion;

/*
 * To illustrate task launches and futures in Legion
 * we implement a program to compute the first N
 * Fibonacci numbers.  While we note that this is not
 * the fastest way to compute Fibonacci numbers, it
 * is designed to showcase the functional nature of
 * Legion tasks and futures.
 */

int numworkers = 4;

enum TaskIDs {
  TOP_LEVEL_TASK_ID,
  WORKER_TASK_ID,
};

PhaseBarrier pb;

void worker_task(const Task *task,
                 const std::vector<PhysicalRegion> &regions,
                 Context ctx, Runtime *runtime)
{
  printf("%s\n", (const char*)task->args);
  pb.arrive();
}

void top_level_task(const Task *task,
                    const std::vector<PhysicalRegion> &regions,
                    Context ctx, Runtime *runtime)
{
  
  pb = runtime->create_phase_barrier(ctx, numworkers);

  const char* phase1 = "Phase 1";
  for(int i=0; i < numworkers; i++){
    TaskLauncher launcher(WORKER_TASK_ID, TaskArgument(phase1,sizeof(char*)));
    runtime->execute_task(ctx, launcher);
  }

  const char* phase2 = "Phase 2";
  for(int i=0; i < numworkers; i++){
    TaskLauncher launcher(WORKER_TASK_ID, TaskArgument(phase2,sizeof(char*)));
    runtime->execute_task(ctx, launcher);
  }
   
}

int main(int argc, char **argv)
{
  if(argc > 1) 
    numworkers = atoi(argv[1]);

  Runtime::set_top_level_task_id(TOP_LEVEL_TASK_ID);
  Runtime::register_legion_task<top_level_task>(TOP_LEVEL_TASK_ID,
      Processor::LOC_PROC, true/*single*/, false/*index*/);
  // Note that tasks which return values must pass the type of
  // the return argument as the first template parameter.
  Runtime::register_legion_task<worker_task>(WORKER_TASK_ID,
      Processor::LOC_PROC, true/*single*/, false/*index*/);
  // The sum-task has a very special property which is that it is
  // guaranteed never to make any runtime calls.  We call these
  // kinds of tasks "leaf" tasks and tell the runtime system
  // about them using the 'TaskConfigOptions' struct.  Being
  // a leaf task allows the runtime to perform significant
  // optimizations that minimize the overhead of leaf task
  // execution.  Note that we also tell the runtime to 
  // automatically generate the variant ID for this task
  // with the 'AUTO_GENERATE_ID' argument.

  return Runtime::start(argc, argv);
}
