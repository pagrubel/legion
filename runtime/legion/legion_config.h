/* Copyright 2016 Stanford University, NVIDIA Corporation
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


#ifndef __LEGION_CONFIG_H__
#define __LEGION_CONFIG_H__

/**
 * \file legion_config.h
 */

// ******************** IMPORTANT **************************
//
// This file is PURE C, **NOT** C++. Keep any C++-isms in
// legion_types.h, or elsewhere.
//
// ******************** IMPORTANT **************************

#include "lowlevel_config.h"

//==========================================================================
//                                Constants
//==========================================================================

#define AUTO_GENERATE_ID   UINT_MAX

#ifndef MAX_RETURN_SIZE
#define MAX_RETURN_SIZE    2048 // maximum return type size in bytes
#endif

#ifndef MAX_FIELDS
#define MAX_FIELDS         512 // must be a power of 2
#endif

// Some default values

// The maximum number of nodes to be run on
#ifndef MAX_NUM_NODES
#define MAX_NUM_NODES                   1024
#endif
// The maximum number of processors on a node
#ifndef MAX_NUM_PROCS
#define MAX_NUM_PROCS                   64
#endif
// Default number of mapper slots
#ifndef DEFAULT_MAPPER_SLOTS
#define DEFAULT_MAPPER_SLOTS            8
#endif
// Default number of contexts made for each runtime instance
// Ideally this is a power of 2 (better for performance)
#ifndef DEFAULT_CONTEXTS
#define DEFAULT_CONTEXTS                8
#endif
// Maximum number of sub-tasks per task at a time
#ifndef DEFAULT_MAX_TASK_WINDOW
#define DEFAULT_MAX_TASK_WINDOW         1024
#endif
// Default amount of hysteresis on the task window in the
// form of a percentage (must be between 0 and 100)
#ifndef DEFAULT_TASK_WINDOW_HYSTERESIS
#define DEFAULT_TASK_WINDOW_HYSTERESIS  75
#endif
// How many tasks to group together for runtime operations
#ifndef DEFAULT_MIN_TASKS_TO_SCHEDULE
#define DEFAULT_MIN_TASKS_TO_SCHEDULE   32
#endif
// Scheduling granularity for how many operations to
// handle at a time at each stage of the pipeline
#ifndef DEFAULT_SUPERSCALAR_WIDTH
#define DEFAULT_SUPERSCALAR_WIDTH       4
#endif
// The maximum size of active messages sent by the runtime in bytes
// Note this value was picked based on making a tradeoff between
// latency and bandwidth numbers on both Cray and Infiniband
// interconnect networks.
#ifndef DEFAULT_MAX_MESSAGE_SIZE
#define DEFAULT_MAX_MESSAGE_SIZE        16384
#endif
// Timeout before checking for whether a logical user
// should be pruned from the logical region tree data strucutre
// Making the value less than or equal to zero will
// result in checks always being performed
#ifndef DEFAULT_LOGICAL_USER_TIMEOUT
#define DEFAULT_LOGICAL_USER_TIMEOUT    32
#endif
// Number of events to place in each GC epoch
// Large counts improve efficiency but add latency to
// garbage collection.  Smaller count reduce efficiency
// but improve latency of collection.
#ifndef DEFAULT_GC_EPOCH_SIZE
#define DEFAULT_GC_EPOCH_SIZE           64
#endif

// Used for debugging memory leaks
// How often tracing information is dumped
// based on the number of scheduler invocations
#ifndef TRACE_ALLOCATION_FREQUENCY
#define TRACE_ALLOCATION_FREQUENCY      1024
#endif

// The maximum alignment guaranteed on the 
// target machine bytes.  For most 64-bit 
// systems this should be 16 bytes.
#ifndef LEGION_MAX_ALIGNMENT
#define LEGION_MAX_ALIGNMENT            16
#endif

// Give an ideal upper bound on the maximum
// number of operations Legion should keep
// available for recycling. Where possible
// the runtime will delete objects to keep
// overall memory usage down.
#ifndef LEGION_MAX_RECYCLABLE_OBJECTS
#define LEGION_MAX_RECYCLABLE_OBJECTS      1024
#endif

// An initial seed for random numbers
// generated by the high-level runtime.
#ifndef LEGION_INIT_SEED
#define LEGION_INIT_SEED                  0x221B
#endif

// Some helper macros

// This statically computes an integer log base 2 for a number
// which is guaranteed to be a power of 2. Adapted from
// http://graphics.stanford.edu/~seander/bithacks.html#IntegerLogDeBruijn
#define STATIC_LOG2(x)  (LOG2_LOOKUP((uint32_t)(x * 0x077CB531U) >> 27))
#define LOG2_LOOKUP(x) ((x==0) ? 0 : (x==1) ? 1 : (x==2) ? 28 : (x==3) ? 2 : \
                   (x==4) ? 29 : (x==5) ? 14 : (x==6) ? 24 : (x==7) ? 3 : \
                   (x==8) ? 30 : (x==9) ? 22 : (x==10) ? 20 : (x==11) ? 15 : \
                   (x==12) ? 25 : (x==13) ? 17 : (x==14) ? 4 : (x==15) ? 8 : \
                   (x==16) ? 31 : (x==17) ? 27 : (x==18) ? 13 : (x==19) ? 23 : \
                   (x==20) ? 21 : (x==21) ? 19 : (x==22) ? 16 : (x==23) ? 7 : \
                   (x==24) ? 26 : (x==25) ? 12 : (x==26) ? 18 : (x==27) ? 6 : \
                   (x==28) ? 11 : (x==29) ? 5 : (x==30) ? 10 : 9)

#ifndef FIELD_LOG2
#define FIELD_LOG2         STATIC_LOG2(MAX_FIELDS) // log2(MAX_FIELDS)
#endif

// The following enums are all re-exported by
// LegionRuntime::HighLevel. These versions are here to facilitate the
// C API. If you are writing C++ code, use the namespaced versions.

typedef enum legion_error_t {
  NO_ERROR = 0,
  ERROR_RESERVED_REDOP_ID = 1,
  ERROR_DUPLICATE_REDOP_ID = 2,
  ERROR_RESERVED_TYPE_HANDLE = 3,
  ERROR_DUPLICATE_TYPE_HANDLE = 4,
  ERROR_DUPLICATE_FIELD_ID = 5,
  ERROR_PARENT_TYPE_HANDLE_NONEXISTENT = 6,
  ERROR_MISSING_PARENT_FIELD_ID = 7,
  ERROR_RESERVED_PROJECTION_ID = 8,
  ERROR_DUPLICATE_PROJECTION_ID = 9,
  ERROR_UNREGISTERED_VARIANT = 10,
  ERROR_USE_REDUCTION_REGION_REQ = 11,
  ERROR_INVALID_ACCESSOR_REQUESTED = 12,
  ERROR_PHYSICAL_REGION_UNMAPPED = 13,
  ERROR_RESERVED_TASK_ID = 14,
  ERROR_INVALID_ARG_MAP_DESTRUCTION = 15,
  ERROR_RESERVED_MAPPING_ID = 16,
  ERROR_BAD_INDEX_PRIVILEGES = 17,
  ERROR_BAD_FIELD_PRIVILEGES = 18,
  ERROR_BAD_REGION_PRIVILEGES = 19,
  ERROR_BAD_PARTITION_PRIVILEGES = 20,
  ERROR_BAD_PARENT_INDEX = 21,
  ERROR_BAD_INDEX_PATH = 22,
  ERROR_BAD_PARENT_REGION = 23,
  ERROR_BAD_REGION_PATH = 24,
  ERROR_BAD_PARTITION_PATH = 25,
  ERROR_BAD_FIELD = 26,
  ERROR_BAD_REGION_TYPE = 27,
  ERROR_INVALID_TYPE_HANDLE = 28,
  ERROR_LEAF_TASK_VIOLATION = 29,
  ERROR_INVALID_REDOP_ID = 30,
  ERROR_REDUCTION_INITIAL_VALUE_MISMATCH = 31,
  ERROR_INVALID_UNMAP_OP = 32,
  ERROR_INVALID_DUPLICATE_MAPPING = 33,
  ERROR_INVALID_REGION_ARGUMENT_INDEX = 34,
  ERROR_INVALID_MAPPING_ACCESS = 35,
  ERROR_STALE_INLINE_MAPPING_ACCESS = 36,
  ERROR_INVALID_INDEX_SPACE_PARENT = 37,
  ERROR_INVALID_INDEX_PART_PARENT = 38,
  ERROR_INVALID_INDEX_SPACE_COLOR = 39,
  ERROR_INVALID_INDEX_PART_COLOR = 40,
  ERROR_INVALID_INDEX_SPACE_HANDLE = 41,
  ERROR_INVALID_INDEX_PART_HANDLE = 42,
  ERROR_FIELD_SPACE_FIELD_MISMATCH = 43,
  ERROR_INVALID_INSTANCE_FIELD = 44,
  ERROR_DUPLICATE_INSTANCE_FIELD = 45,
  ERROR_TYPE_INST_MISMATCH = 46,
  ERROR_TYPE_INST_MISSIZE = 47,
  ERROR_INVALID_INDEX_SPACE_ENTRY = 48,
  ERROR_INVALID_INDEX_PART_ENTRY = 49,
  ERROR_INVALID_FIELD_SPACE_ENTRY = 50,
  ERROR_INVALID_REGION_ENTRY = 51,
  ERROR_INVALID_PARTITION_ENTRY = 52,
  ERROR_ALIASED_INTRA_TASK_REGIONS = 53,
  ERROR_MAX_FIELD_OVERFLOW = 54,
  ERROR_MISSING_TASK_COLLECTION = 55,
  ERROR_INVALID_IDENTITY_PROJECTION_USE = 56,
  ERROR_INVALID_PROJECTION_ID = 57,
  ERROR_NON_DISJOINT_PARTITION = 58,
  ERROR_BAD_PROJECTION_USE = 59,
  ERROR_INDEPENDENT_SLICES_VIOLATION = 60,
  ERROR_INVALID_REGION_HANDLE = 61,
  ERROR_INVALID_PARTITION_HANDLE = 62,
  ERROR_VIRTUAL_MAP_IN_LEAF_TASK = 63,
  ERROR_LEAF_MISMATCH = 64,
  ERROR_INVALID_PROCESSOR_SELECTION = 65,
  ERROR_INVALID_VARIANT_SELECTION = 66,
  ERROR_INVALID_MAPPER_OUTPUT = 67,
  ERROR_UNINITIALIZED_REDUCTION = 68,
  ERROR_INVALID_INDEX_DOMAIN = 69,
  ERROR_INVALID_INDEX_PART_DOMAIN = 70,
  ERROR_DISJOINTNESS_TEST_FAILURE = 71,
  ERROR_NON_DISJOINT_TASK_REGIONS = 72,
  ERROR_INVALID_FIELD_ACCESSOR_PRIVILEGES = 73,
  ERROR_INVALID_PREMAPPED_REGION_LOCATION = 74,
  ERROR_IDEMPOTENT_MISMATCH = 75,
  ERROR_INVALID_MAPPER_ID = 76,
  ERROR_INVALID_TREE_ENTRY = 77,
  ERROR_SEPARATE_UTILITY_PROCS = 78,
  ERROR_MAXIMUM_NODES_EXCEEDED = 79,
  ERROR_MAXIMUM_PROCS_EXCEEDED = 80,
  ERROR_INVALID_TASK_ID = 81,
  ERROR_INVALID_MAPPER_DOMAIN_SLICE = 82,
  ERROR_UNFOLDABLE_REDUCTION_OP = 83,
  ERROR_INVALID_INLINE_ID = 84,
  ERROR_ILLEGAL_MUST_PARALLEL_INLINE = 85,
  ERROR_RETURN_SIZE_MISMATCH = 86,
  ERROR_ACCESSING_EMPTY_FUTURE = 87,
  ERROR_ILLEGAL_PREDICATE_FUTURE = 88,
  ERROR_COPY_REQUIREMENTS_MISMATCH = 89,
  ERROR_INVALID_COPY_FIELDS_SIZE = 90,
  ERROR_COPY_SPACE_MISMATCH = 91,
  ERROR_INVALID_COPY_PRIVILEGE = 92,
  ERROR_INVALID_PARTITION_COLOR = 93,
  ERROR_EXCEEDED_MAX_CONTEXTS = 94,
  ERROR_ACQUIRE_MISMATCH = 95,
  ERROR_RELEASE_MISMATCH = 96,
  ERROR_INNER_LEAF_MISMATCH = 97,
  ERROR_INVALID_FIELD_PRIVILEGES = 98,
  ERROR_ILLEGAL_NESTED_TRACE = 99,
  ERROR_UNMATCHED_END_TRACE = 100,
  ERROR_CONFLICTING_PARENT_MAPPING_DEADLOCK = 101,
  ERROR_CONFLICTING_SIBLING_MAPPING_DEADLOCK = 102,
  ERROR_INVALID_PARENT_REQUEST = 103,
  ERROR_INVALID_FIELD_ID = 104,
  ERROR_NESTED_MUST_EPOCH = 105,
  ERROR_UNMATCHED_MUST_EPOCH = 106,
  ERROR_MUST_EPOCH_FAILURE = 107,
  ERROR_DOMAIN_DIM_MISMATCH = 108,
  ERROR_INVALID_PROCESSOR_NAME = 109,
  ERROR_INVALID_INDEX_SUBSPACE_REQUEST = 110,
  ERROR_INVALID_INDEX_SUBPARTITION_REQUEST = 111,
  ERROR_INVALID_FIELD_SPACE_REQUEST = 112,
  ERROR_INVALID_LOGICAL_SUBREGION_REQUEST = 113,
  ERROR_INVALID_LOGICAL_SUBPARTITION_REQUEST = 114,
  ERROR_ALIASED_REGION_REQUIREMENTS = 115,
  ERROR_MISSING_DEFAULT_PREDICATE_RESULT = 116,
  ERROR_PREDICATE_RESULT_SIZE_MISMATCH = 117,
  ERROR_MPI_INTEROPERABILITY_NOT_CONFIGURED = 118,
  ERROR_TRACING_ALLOCATION_WITH_SEPARATE = 119,
  ERROR_EMPTY_INDEX_PARTITION = 120,
  ERROR_INCONSISTENT_SEMANTIC_TAG = 121,
  ERROR_INVALID_SEMANTIC_TAG = 122,
  ERROR_DUMMY_CONTEXT_OPERATION = 123,
  ERROR_INVALID_CONTEXT_CONFIGURATION = 124,
  ERROR_INDEX_TREE_MISMATCH = 125,
  ERROR_INDEX_PARTITION_ANCESTOR = 126,
  ERROR_INVALID_PENDING_CHILD = 127,
  ERROR_ILLEGAL_FILE_ATTACH = 128,
  ERROR_ILLEGAL_ALLOCATOR_REQUEST = 129,
  ERROR_ILLEGAL_DETACH_OPERATION = 130,
  ERROR_NO_PROCESSORS = 131,
  ERROR_ILLEGAL_REDUCTION_VIRTUAL_MAPPING = 132,
  ERROR_INVALID_MAPPED_REGION_LOCATION = 133,
  ERROR_RESERVED_SERDEZ_ID = 134,
  ERROR_DUPLICATE_SERDEZ_ID = 135,
  ERROR_INVALID_SERDEZ_ID = 136,
  ERROR_TRACE_VIOLATION = 137,
  ERROR_INVALID_TARGET_PROC = 138,
  ERROR_INCOMPLETE_TRACE = 139,
  ERROR_STATIC_CALL_POST_RUNTIME_START = 140,
  ERROR_ILLEGAL_GLOBAL_VARIANT_REGISTRATION = 141,
  ERROR_ILLEGAL_USE_OF_NON_GLOBAL_VARIANT = 142,
  ERROR_RESERVED_CONSTRAINT_ID = 143,
  ERROR_DUPLICATE_CONSTRAINT_ID = 144,
  ERROR_INVALID_CONSTRAINT_ID = 145,
}  legion_error_t;

// enum and namepsaces don't really get along well
typedef enum legion_privilege_mode_t {
  NO_ACCESS       = 0x00000000, 
  READ_ONLY       = 0x00000001,
  READ_WRITE      = 0x00000007, // All three privileges
  WRITE_ONLY      = 0x00000002, // same as WRITE_DISCARD
  WRITE_DISCARD   = 0x00000002, // same as WRITE_ONLY
  REDUCE          = 0x00000004,
  PROMOTED        = 0x00001000, // Internal use only
} legion_privilege_mode_t;

typedef enum legion_allocate_mode_t {
  NO_MEMORY       = 0x00000000,
  ALLOCABLE       = 0x00000001,
  FREEABLE        = 0x00000002,
  MUTABLE         = 0x00000003,
  REGION_CREATION = 0x00000004,
  REGION_DELETION = 0x00000008,
  ALL_MEMORY      = 0x0000000F,
} legion_allocate_mode_t;

typedef enum legion_coherence_property_t {
  EXCLUSIVE    = 0,
  ATOMIC       = 1,
  SIMULTANEOUS = 2,
  RELAXED      = 3,
} legion_coherence_property_t;

// Optional region requirement flags
typedef enum legion_region_flags_t {
  NO_FLAG         = 0x00000000,
  VERIFIED_FLAG   = 0x00000001,
  NO_ACCESS_FLAG  = 0x00000002,
} legion_region_flags_T;

typedef enum legion_index_space_kind_t {
  UNSTRUCTURED_KIND,
  SPARSE_ARRAY_KIND,
  DENSE_ARRAY_KIND,
} legion_index_space_kind_t;

typedef enum legion_handle_type_t {
  SINGULAR, // a single logical region
  PART_PROJECTION, // projection from a partition
  REG_PROJECTION, // projection from a region
} legion_handle_type_t;

typedef enum legion_partition_kind_t {
  DISJOINT_KIND,
  ALIASED_KIND,
  COMPUTE_KIND,
} legion_partition_kind_t;

typedef enum legion_dependence_type_t {
  NO_DEPENDENCE = 0,
  TRUE_DEPENDENCE = 1,
  ANTI_DEPENDENCE = 2, // Write-After-Read or Write-After-Write with Write-Only privilege
  ATOMIC_DEPENDENCE = 3,
  SIMULTANEOUS_DEPENDENCE = 4,
  PROMOTED_DEPENDENCE = 5,
} legion_dependence_type_t;

enum {
  NAME_SEMANTIC_TAG = 0,
  FIRST_AVAILABLE_SEMANTIC_TAG = 1,
};

//==========================================================================
//                                Types
//==========================================================================

typedef legion_lowlevel_file_mode_t legion_file_mode_t;
typedef legion_lowlevel_processor_kind_t legion_processor_kind_t;
typedef legion_lowlevel_memory_kind_t legion_memory_kind_t;
typedef legion_lowlevel_domain_max_rect_dim_t legion_domain_max_rect_dim_t;
typedef legion_lowlevel_reduction_op_id_t legion_reduction_op_id_t;
typedef legion_lowlevel_custom_serdez_id_t legion_custom_serdez_id_t;
typedef legion_lowlevel_address_space_t legion_address_space_t;
typedef int legion_task_priority_t;
typedef unsigned int legion_color_t;
typedef unsigned int legion_field_id_t;
typedef unsigned int legion_trace_id_t;
typedef unsigned int legion_mapper_id_t;
typedef unsigned int legion_context_id_t;
typedef unsigned int legion_instance_id_t;
typedef unsigned int legion_index_space_id_t;
typedef unsigned int legion_index_partition_id_t;
typedef unsigned int legion_index_tree_id_t;
typedef unsigned int legion_field_space_id_t;
typedef unsigned int legion_generation_id_t;
typedef unsigned int legion_type_handle;
typedef unsigned int legion_projection_id_t;
typedef unsigned int legion_region_tree_id_t;
typedef unsigned int legion_address_space_id_t;
typedef unsigned int legion_tunable_id_t;
typedef unsigned long legion_distributed_id_t;
typedef unsigned long legion_mapping_tag_id_t;
typedef unsigned long legion_variant_id_t;
typedef unsigned long legion_semantic_tag_t;
typedef unsigned long long legion_unique_id_t;
typedef unsigned long long legion_version_id_t;
typedef legion_lowlevel_task_func_id_t legion_task_id_t;
typedef unsigned long legion_layout_constraint_id_t;


#endif // __LEGION_CONFIG_H__
