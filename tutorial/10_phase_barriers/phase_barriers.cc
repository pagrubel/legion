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

int numworkers = 4;

enum TaskIDs {
  TOP_LEVEL_TASK_ID,
  WORKER_TASK_ID,
};

PhaseBarrier p1comp;
PhaseBarrier p2comp;

void worker_task(const Task *task,
                 const std::vector<PhysicalRegion> &regions,
                 Context ctx, Runtime *runtime)
{
  printf("%s\n", (const char*)task->args);
}

void top_level_task(const Task *task,
                    const std::vector<PhysicalRegion> &regions,
                    Context ctx, Runtime *runtime)
{
  p1comp = runtime->create_phase_barrier(ctx, numworkers);
  p1comp = runtime->advance_phase_barrier(ctx, p1comp);

  p2comp = runtime->create_phase_barrier(ctx, numworkers);
  p2comp = runtime->advance_phase_barrier(ctx, p2comp); 
  
  // We spawn phase 2, but make it dependent on phase 1 completing
  const char* phase2 = "Phase 2";
  for(int i=0; i < numworkers; i++){
    TaskLauncher launcher(WORKER_TASK_ID, TaskArgument(phase2,sizeof(char*)));
    launcher.add_wait_barrier(p1comp);
    launcher.add_arrival_barrier(p2comp);
    runtime->execute_task(ctx, launcher);
  }

  // We spawn phase 1 without any dependencies
  const char* phase1 = "Phase 1";
  for(int i=0; i < numworkers; i++){
    TaskLauncher launcher(WORKER_TASK_ID, TaskArgument(phase1,sizeof(char*)));
    launcher.add_arrival_barrier(p1comp);
    runtime->execute_task(ctx, launcher);
  }

  // When phase 2 barrier is complete, we can destroy both
  p2comp.wait();
  printf("Phase 2 complete, destroying barriers\n");
  runtime->destroy_phase_barrier(ctx, p1comp);
  runtime->destroy_phase_barrier(ctx, p2comp);
}

int main(int argc, char **argv)
{
  if(argc > 1) 
    numworkers = atoi(argv[1]);

  Runtime::register_legion_task<top_level_task>(TOP_LEVEL_TASK_ID,
      Processor::LOC_PROC, true, false);

  Runtime::register_legion_task<worker_task>(WORKER_TASK_ID,
      Processor::LOC_PROC, true, false);

  Runtime::set_top_level_task_id(TOP_LEVEL_TASK_ID);

  return Runtime::start(argc, argv);
}
