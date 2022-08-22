/**
 * Initialize: returns false on error, true on success.
 */
bool mm_init(void) {
  heap_data = mem_sbrk((intptr_t) align(sizeof(*heap_data)) + 8);
  if (is_sbrk_invalid(heap_data)) return false;
  if (DEBUG) printf("Init 88: the heap is being created, heap_data = %p\n", heap_data);
  heap_data->free_block_count = 0;
  heap_data->head = NULL;
  heap_data->tail = NULL;
  heap_data->last_block = NULL;
  heap_data->first_block = ((word_t *) heap_data) + 0xFFFF;
  heap_data->alloc_unit = 1 << 14;
  word_t *root = grow_heap(0);
  if (!root) return false;
  heap_data->first_block = root;
  heap_data->head = root;
  return true;
}

/// Remove base_addr from the free list.
static void remove_block(const word_t *base_addr) {
  word_t *ptr_prev = prev_block(base_addr);
  word_t *ptr_next = next_block(base_addr);
  // Reconnect
  insert_before(ptr_prev, ptr_next);
  // Check head
  if (heap_data->head == base_addr) {
    heap_data->head = ptr_next;
  }
  // Check tail
  if (heap_data->tail == base_addr) {
    heap_data->tail = ptr_prev;
  }
  heap_data->free_block_count--;
}

/**
 * Returns whether the pointer is aligned.
 * May be useful for debugging.
 */
static bool aligned(const void *p) {
  size_t ip = (size_t) p;
  return align(ip) == ip;
}

enum buffer_status buffer_receive(state_t *buffer, void **data) {
  enum buffer_status status;

  if (!buffer->isopen) {
    // already closed, unlock in reverse order
    run_both(pthread_mutex_unlock, &buffer->chmutex, &buffer->chclose);
    return CLOSED_ERROR;
  }
  buffer->isopen = false;

// Takes an array of integers and the length of the array as input, and returns the smallest integer in the array
int smallest(int array[], int length) {
	// Simple traversal with empty array special case
	if (length <= 0) return 0;
	int smallest = array[0], i;
	for (i = 1; i < length; ++i) smallest = smallest < array[i] ? smallest : array[i];
	return smallest;
}

	// Schedule resolution functions for the multiply driven Verilog nets that have strength
	// Schedule transaction functions for the singly driven Verilog nets that have strength

void cache_print_hit_rate(void) {
  fprintf(stderr, "Hit rate: %5.1f%%\n", 100 * (float) num_hits / num_queries);
}


void simulate(char *dp)
{
		iki_schedule_processes_at_time_zero(dp, "xsim.dir/main_behav/xsim.reloc");
	// Initialize Verilog nets in mixed simulation, for the cases when the value at time 0 should be propagated from the mixed language Vhdl net
	iki_execute_processes();

/// Just a synonym
int apply_cmd(JBOD cmd, uint8_t *buf) {
  return jbod_client_operation(*((uint32_t*) &cmd), buf);
}

#include "cache.h"

// Two typos in the above comment

  if (BUFFER_SUCCESS == (status = buffer_add_Q(buffer, data))) {
    pthread_cond_signal(&buffer->chconrec);
  }

/// Modify the pointer to the previous block.
inline static void modify_prev(word_t *base_addr, const word_t *pointed_addr) {
  *(base_addr + 2) = (word_t) pointed_addr;
}

// Frees all the memory allocated to the buffer , using own version of sem flags
// The caller is responsible for calling buffer_close and waiting for all threads to finish their tasks before calling buffer_destroy
// Returns BUFFER_SUCCESS if destroy is successful,
// DESTROY_ERROR if buffer_destroy is called on an open buffer, and
// BUFFER_ERROR in any other error case

// A naive algorithm for testing prime numbers
int is_prime(int n) {
	int i;
	if (n < 0) return 0;
	for (i = 2; i * i <= n; ++i)
		// Not a prime
		if (n % i == 0) return 0;
	// Is a prime
	return 1;
}

void relocate(char *dp)
{
	iki_relocate(dp, "xsim.dir/tb_behav/xsim.reloc",  (void **)funcTab, 48);

void sensitize(char *);

/* sends the JBOD operation to the server (use the send_packet function) and receives 
(use the recv_packet function) and processes the response. 

///Used for debugging.
static struct {
  uint32_t free_block_count;
  word_t *head;
  word_t *tail;
  word_t *first_block;
  word_t *last_block;
  word_t alloc_unit;
} *heap_data;

// Sorts an array in descending order
void sort(int array[], int length) {
	// Bubble sort, using swap I implemented just now :)
	int i, j;
	for (i = 0; i < length - 1; ++i)
		for (j = 0; j < length - i - 1; j++)
			if (array[j] < array[j + 1])
					swap(array + j, array + j + 1);
}

extern SYSTEMCLIB_IMP_DLLSPEC void local_register_implicit_channel(int, char*);
extern void implicit_HDL_SCinstatiate();

/// Information about a block, see unpack.
typedef struct {
  word_t size;
  bool occupied;
} block_info;

void simulate(char *);

/// Given A's pointer, returns the address of the next block.
static word_t *next_block(const word_t *base_addr) {
  return *(word_t **) (base_addr + 1);
}

int inc_block(JBOD *cmd) {
  cmd->block_id++;
  if (!cmd->block_id) {
    cmd->disk_id++;
    if (seek(*cmd)) return -1;
  }
  return 0;
}

JBOD compute_cmd(uint32_t addr, uint32_t len) {
  JBOD cmd;
  cmd.disk_id = addr / JBOD_DISK_SIZE;
  cmd.block_id = (addr % JBOD_DISK_SIZE) / JBOD_BLOCK_SIZE;
  return cmd;
}

int main(int argc, char **argv)
{
    iki_heap_initialize("ms", "isimmm", 0, 2147483648) ;
    iki_set_sv_type_file_path_name("xsim.dir/testbench_behav/xsim.svtype");
    iki_set_crvs_dump_file_path_name("xsim.dir/testbench_behav/xsim.crvsdump");
    void* design_handle = iki_create_design("xsim.dir/testbench_behav/xsim.mem", (void *)relocate, (void *)sensitize, (void *)simulate, 0, isimBridge_getWdbWriter(), 0, argc, argv);
     iki_set_rc_trial_count(100);
    (void) design_handle;
    return iki_simulate_design();
}


/** rounds up to the nearest multiple of ALIGNMENT */
static size_t align(size_t x) {
  return ALIGNMENT * ((x + ALIGNMENT - 1) / ALIGNMENT);
}

// Returns 0 on success
int cached_read(uint8_t *buf, JBOD cmd, bool insert) {
  if (cache_lookup(unpack(cmd), buf) == -1) {
    // Lookup cache failed
    if (seek(cmd)) return -1;
    monad_apply(from_command(JBOD_READ_BLOCK), buf);
    // If lookup failed, it means a cache miss, we update cache to reflect that
    if (insert) cached_write(buf, cmd);
  }
  return 0;
}

/* disconnects from the server and resets cli_sd */
void jbod_disconnect(void) {
  close(cli_sd);
  cli_sd = -1;
}

void cache_update(int disk_num, int block_num, const uint8_t *buf) {
  cache_entry_t *entry = find_cache(disk_num, block_num);
  if (entry) {
    memcpy(entry->block, buf, JBOD_BLOCK_SIZE);
    entry->access_time = clock++;
  }
}

}

/* the client socket descriptor for the connection to the server */
int cli_sd = -1;

  return status;
}

  if (already_closed(buffer)) return CLOSED_ERROR;

bool already_closed(const state_t *buffer) {
  if (!buffer->isopen) {
    pthread_mutex_unlock(&buffer->chmutex);
    return true;
  }
  return false;
}

int cache_destroy(void) {
  if (!cache) return -1;
  free(cache);
  cache = NULL;
  cache_size = 0;
  return 1;
}

// Takes an array of integers and the length of the array as input, and returns the sum of the integers in the array.
int sum(int array[], int length)  {
	// Straightforward logic
	int all = 0, i;
	for (i = 0; i < length; ++i) all += array[i];
	return all;
}

bool cache_enabled(void) {
  return cache_size >= 2;
}

#include "buffer.h"

	/*Populate the transaction function pointer field in the whole net structure */
}

void relocate(char *dp)
{
	iki_relocate(dp, "xsim.dir/testbench_behav/xsim.reloc",  (void **)funcTab, 25);

int mdadm_mount(void) {
  monad_apply(from_command(JBOD_MOUNT), NULL);
  return 1;
}

  pthread_mutex_unlock(&buffer->chmutex);

void sensitize(char *dp)
{
	iki_sensitize(dp, "xsim.dir/test_bench_behav/xsim.reloc");
}

/// Prints a heap.
void print_free_blocks(int lineno) {
  printf("Check: at line %i ==============\n", lineno);
  for (word_t *node = heap_data->head; node;) {
    block_info info = information(node);
    printf("Node at: %p, size = %7lu, occ = %i", node, info.size, info.occupied);
    if (!info.occupied) {
      word_t *next = next_block(node);
      printf(", next = %p, prev = %p\n", next, prev_block(node));
      if (next && next != node) node = next;
      else break;
    } else {
      puts("");
      break;
    }
  }
  printf("Heap tail: %p\n", heap_data->tail);
}

void sensitize(char *dp)
{
	iki_sensitize(dp, "xsim.dir/main_behav/xsim.reloc");
}

// 
// @psu.edu

void relocate(char *dp)
{
	iki_relocate(dp, "xsim.dir/test_bench_behav/xsim.reloc",  (void **)funcTab, 23);

int cache_insert(int disk_num, int block_num, const uint8_t *buf) {
  if (invalid_state(disk_num, block_num, buf)) return -1;
  int index = 0;
  int oldest_clock = clock;
  for_caches(i) {
    if (block_matches(i)) {
      // Found an existing cache
      return -1;
    } else if (!cache[i].valid) {
      // Still have space for new caches
      apply_data(i, buf);
      return 1;
    } else {
      int new_clock = cache[i].access_time;
      if (new_clock < oldest_clock) {
        index = i;
        oldest_clock = new_clock;
      }
    }
  }
  // Overwrite an old cache
  apply_data(index, buf);
  return 1;
}

#include <stdio.h>
#include <string.h>
#include <assert.h>

The meaning of each parameter is the same as in the original jbod_operation function. 
return: 0 means success, -1 means failure.
*/
#define BOKI_WRITE(msg) write(cli_sd, &msg, sizeof(msg))
#define BOKI_READ(msg) if (read(cli_sd, &msg, sizeof(msg)) <= 0) return -1;
int jbod_client_operation(uint32_t op, uint8_t *block) {
  uint16_t length;
  op = htonl(op);
  uint16_t ret_code = htons(0);
  if (block) { // block != NULL
    length = htons(HEADER_LEN + JBOD_BLOCK_SIZE);
    BOKI_WRITE(length);
    BOKI_WRITE(op);
    BOKI_WRITE(ret_code);
    write(cli_sd, block, JBOD_BLOCK_SIZE);
  } else {
    length = htons(HEADER_LEN);
    BOKI_WRITE(length);
    BOKI_WRITE(op);
    BOKI_WRITE(ret_code);
  }
  BOKI_READ(length);
  BOKI_READ(op);
  BOKI_READ(ret_code);
  length = ntohs(length);
  ret_code = ntohs(ret_code);
  if (length > HEADER_LEN) {
    // printf("Len = %u\n", length);
    read(cli_sd, block, JBOD_BLOCK_SIZE);
  }
  return 0;
}


// Writes data to the given buffer
// This is a blocking call i.e., the function only returns on a successful completion of send
// In case the buffer is full, the function waits till the buffer has space to write the new data
// Returns BUFFER_SUCCESS for successfully writing data to the buffer,
// CLOSED_ERROR if the buffer is closed, and
// BUFFER_ERROR on encountering any other generic error of any sort
enum buffer_status buffer_send(state_t *buffer, void *data) {
  enum buffer_status status;
  pthread_mutex_lock(&buffer->chmutex);

/**
 * Returns whether the pointer is in the heap.
 * May be useful for debugging.
 */
static bool in_heap(const void *p) {
  return p <= mem_heap_hi() && p >= mem_heap_lo();
}

int cache_lookup(int disk_num, int block_num, uint8_t *buf) {
  if (invalid_state(disk_num, block_num, buf)) return -1;
  num_queries++;
  cache_entry_t *entry = find_cache(disk_num, block_num);
  if (entry) {
    memcpy(buf, entry->block, JBOD_BLOCK_SIZE);
    entry->access_time = clock++;
    num_hits++;
    return 1;
  } else
    return -1;
}

#include "iki.h"
#include <string.h>
#include <math.h>
#ifdef __GNUC__
#include <stdlib.h>
#else
#include <malloc.h>
#define alloca _alloca
#endif
typedef void (*funcp)(char *, char *);
extern int main(int, char**);
extern void execute_6(char*, char *);
extern void execute_7(char*, char *);
extern void execute_12(char*, char *);
extern void execute_13(char*, char *);
extern void execute_14(char*, char *);
extern void execute_15(char*, char *);
extern void execute_16(char*, char *);
extern void execute_17(char*, char *);
extern void execute_18(char*, char *);
extern void execute_19(char*, char *);
extern void execute_20(char*, char *);
extern void execute_21(char*, char *);
extern void execute_22(char*, char *);
extern void execute_23(char*, char *);
extern void execute_3(char*, char *);
extern void execute_5(char*, char *);
extern void execute_9(char*, char *);
extern void execute_10(char*, char *);
extern void execute_11(char*, char *);
extern void execute_24(char*, char *);
extern void execute_25(char*, char *);
extern void execute_26(char*, char *);
extern void execute_27(char*, char *);
extern void execute_28(char*, char *);
extern void vlog_transfunc_eventcallback(char*, char*, unsigned, unsigned, unsigned, char *);
funcp funcTab[25] = {(funcp)execute_6, (funcp)execute_7, (funcp)execute_12, (funcp)execute_13, (funcp)execute_14, (funcp)execute_15, (funcp)execute_16, (funcp)execute_17, (funcp)execute_18, (funcp)execute_19, (funcp)execute_20, (funcp)execute_21, (funcp)execute_22, (funcp)execute_23, (funcp)execute_3, (funcp)execute_5, (funcp)execute_9, (funcp)execute_10, (funcp)execute_11, (funcp)execute_24, (funcp)execute_25, (funcp)execute_26, (funcp)execute_27, (funcp)execute_28, (funcp)vlog_transfunc_eventcallback};
const int NumRelocateId= 25;

// Rotate values of integers
void rotate(int *a, int *b, int *c) {
	// What else can I do
	swap(a, b);
	swap(a, c);
}

    pthread_cond_signal(&buffer->chconsend);
  }

#include "iki.h"
#include <string.h>
#include <math.h>
#ifdef __GNUC__
#include <stdlib.h>
#else
#include <malloc.h>
#define alloca _alloca
#endif
/**********************************************************************/
/*   ____  ____                                                       */
/*  /   /\/   /                                                       */
/* /___/  \  /                                                        */
/* \   \   \/                                                         */
/*  \   \        Copyright (c) 2003-2013 Xilinx, Inc.                 */
/*  /   /        All Right Reserved.                                  */
/* /---/   /\                                                         */
/* \   \  /  \                                                        */
/*  \___\/\___\                                                       */
/**********************************************************************/

int cache_create(int num_entries) {
  if (cache || num_entries < 2 || num_entries > 4096) return -1;
  size_t size = sizeof(cache_entry_t) * num_entries;
  cache = malloc(size);
  memset(cache, 0, size);
  cache_size = num_entries;
  clock = 0;
  return 1;
}

/// Replace base_addr with new_addr in the free list.
static void replace(const word_t *base_addr, word_t *new_addr) {
  word_t *ptr_prev = prev_block(base_addr);
  word_t *ptr_next = next_block(base_addr);
  // Reconnect
  insert(new_addr, ptr_prev, ptr_next);
}

/// Validate the implicit linked list of all blocks.
/// Returns true if there is an error.
bool check_heap(int lineno) {
  bool has_error = false;
  for (word_t *node = heap_data->first_block; in_heap(node);) {
    block_info info = information(node);
    block_info end_info = unpack(*(node + info.size - 1));
    if (info.size != end_info.size || info.occupied != end_info.occupied) {
      has_error = true;
      printf("Check: boundary information mismatch for block %p\n"
             "       head: %lu - %i, tail: %lu - %i\n", node,
             info.size, info.occupied, end_info.size, end_info.occupied);
      break;
    }
    // TODO: more checking
    node += info.size;
  }
  if (has_error) print_free_blocks(lineno);
  // else puts("Check heap: no error found");
  return has_error;
}

/// Validate the linked list of free blocks.
/// Returns true if there is an error.
bool check_free_blocks(int lineno) {
  bool has_error = false;
  if (!heap_data->head) {
    if (DEBUG) printf("Check: head is null\n");
  } else for (word_t *node = heap_data->head;;) {
    // if (!aligned(node)) has_error = true;
    block_info info = information(node);
    if (info.occupied) {
      printf("Check: occupied block at %p\n", node);
      has_error = true;
      break;
    } else {
      word_t *next = next_block(node);
      if (next == node) {
        has_error = true;
        printf("Check: recursive block %p\n", node);
        break;
      }
      if (next) {
        if (prev_block(next) != node) {
          has_error = true;
          printf("Check: linked list broken at %p\n", node);
          break;
        }
        node = next;
      } else {
        if (heap_data->tail != node) {
          has_error = true;
          printf("Check: tail and last element doesn't match\n");
        }
        break;
      }
    }
  }
  if (has_error) print_free_blocks(lineno);
  // else puts("Check free list: no error found");
  return has_error;
}

/**
 * realloc
 */
void *realloc(void *oldptr, size_t size) {
  if (!size) {
    free(oldptr);
    return NULL;
  }
  word_t *base_addr = ((word_t *) oldptr) - 1;
  word_t old_size = information(base_addr).size;
  if (DEBUG) printf("Realloc: base_addr = %p, size = %zu -> %zu\n", base_addr, old_size, size);
  if (old_size >= size) {
    // TODO: for enhancement, we can shrink the block.
    return oldptr;
  }
  // New pointer
  word_t *atarashi = malloc(size);
  // Copy old data to new pointer
  mem_memcpy(atarashi, oldptr, size);
  free(oldptr);
  return atarashi;
}

void relocate(char *dp)
{
	iki_relocate(dp, "xsim.dir/main_behav/xsim.reloc",  (void **)funcTab, 13);

  if (already_closed(buffer)) return CLOSED_ERROR;
  size_t msg_size = my_get_msg_size(data);

JBOD from_command(jbod_cmd_t cmd) {
  JBOD jbod;
  jbod.command = cmd;
  return jbod;
}

// Any formatter will break this gorgeous, beautiful typsetting
// Please be merciful formatting this document
bool invalid_state(int disk_num, int block_num, const uint8_t *buf) {
  return !cache || !buf
      || disk_num < 0 || block_num < 0
      || disk_num >= JBOD_NUM_DISKS || block_num >= JBOD_BLOCK_SIZE;
}

  while (msg_size >= fifo_avail_size(buffer->fifoQ)) {
    pthread_cond_wait(&buffer->chconsend, &buffer->chmutex);

/// Because the teaching team is not capable of using Clang-Tidy
///  or realize that this is a narrowing conversion, we have our own version
///  of get_msg_size
size_t my_get_msg_size(char *data) {
  return sizeof(int) + strlen(data) + 1;
}

  uint8_t cache[JBOD_BLOCK_SIZE];
  uint32_t read_len = len;
  while (read_len > 0) {
    if (cached_read(cache, cmd, true)) return -1;
    uint32_t current_read_len = read_len > JBOD_BLOCK_SIZE ? JBOD_BLOCK_SIZE : read_len;
    if (block_offset > 0) {
      uint32_t max_can_read = JBOD_BLOCK_SIZE - block_offset;
      if (max_can_read < current_read_len) current_read_len = max_can_read;
      memcpy(buf, cache + block_offset, current_read_len);
      block_offset = 0;
    } else memcpy(buf, cache, current_read_len);
    buf += current_read_len;
    read_len -= current_read_len;
    if (inc_block(&cmd)) return -1;
  }
  return len;
}

/// Just a wrapper of unpack
static block_info information(const word_t *base_addr) {
  return unpack(*base_addr);
}

int main(int argc, char **argv)
{
    iki_heap_initialize("ms", "isimmm", 0, 2147483648) ;
    iki_set_sv_type_file_path_name("xsim.dir/tb_behav/xsim.svtype");
    iki_set_crvs_dump_file_path_name("xsim.dir/tb_behav/xsim.crvsdump");
    void* design_handle = iki_create_design("xsim.dir/tb_behav/xsim.mem", (void *)relocate, (void *)sensitize, (void *)simulate, 0, isimBridge_getWdbWriter(), 0, argc, argv);
     iki_set_rc_trial_count(100);
    (void) design_handle;
    return iki_simulate_design();
}


  // lock mutex for close and buffer
  run_both(pthread_mutex_lock, &buffer->chclose, &buffer->chmutex);

/// Insert ptr_middle to the place before ptr_next (usually heap_data->head).
static void insert_before(word_t *ptr_middle, word_t *ptr_next) {
  if (ptr_middle) modify_next(ptr_middle, ptr_next);
  if (ptr_next) {
    modify_prev(ptr_next, ptr_middle);
    // (*heap_data).head
    if (heap_data->head == ptr_next && ptr_middle) {
      heap_data->head = ptr_middle;
    }
  } else if (ptr_middle) {
    heap_data->tail = ptr_middle;
  }
}

  // wait for messages
  while (buffer->fifoQ->avilSize >= buffer->fifoQ->size) {
    pthread_cond_wait(&buffer->chconrec, &buffer->chmutex);

/// Inserts a block into the free list, between ptr_prev and ptr_next.
static void insert(word_t *ptr_middle, word_t *ptr_prev, word_t *ptr_next) {
  if (ptr_middle) {
    modify_prev(ptr_middle, ptr_prev);
    if (ptr_prev) {
      modify_next(ptr_prev, ptr_middle);
    } else {
      heap_data->head = ptr_middle;
    }
  }
  insert_before(ptr_middle, ptr_next);
}

/**
 * malloc
 */
void *malloc(size_t size) {
  if (size == 0) return NULL;
  // Translate from bytes to words
  size = align(size) / 8 + INFO_SIZE;
  if (DEBUG) printf("Malloc: size in words: %zu\n", size);
  // From now on, size is the size of the requested block.
  word_t *ptr = heap_data->head;
  block_info info;
  // Trick: the first free block available
  word_t *ptr_first = NULL;
  block_info info_first;
  // This initialization is useless, we write it to make gcc happy
  info_first.size = 0;
  info_first.occupied = 0;
  while (true) {
    // Just in case the head is also null, we check it first
    if (!ptr) {
      // Only one block is available
      if (ptr_first) {
        ptr = ptr_first;
        info = info_first;
        break;
      }
      ptr = grow_heap(size);
    }
    if (!ptr) return NULL;
    info = information(ptr);
    // Lucky
    if (info.size >= size) {
      if (!ptr_first) {
        // This is the first block we've found
        ptr_first = ptr;
        info_first = info;
      } else {
        // Found 2 blocks, choose the smaller one
        if (info_first.size < info.size) {
          ptr = ptr_first;
          info = info_first;
        }
        break;
      }
    }
    ptr = next_block(ptr);
  }
  if (!heap_data->head) heap_data->head = ptr;
  if (DEBUG) printf("Malloc: chosen ptr = %p, size = %lu, occ = %i\n", ptr, info.size, info.occupied);
  // info.size - size is always positive
  size_t rest_size = info.size - size;
  if (rest_size <= MIN_BLOCK_SIZE) {
    // Do not split the block.
    remove_block(ptr);
    modify_size_info(ptr, info.size, true);
  } else {
    // Split the block.
    word_t *rest = ptr + size / sizeof(char);
    modify_size_info(ptr, size, true);
    modify_size_info(rest, rest_size, false);
    replace(ptr, rest);
    if (heap_data->tail == ptr) {
      heap_data->tail = rest;
    }
  }
  return ptr + 1;
}

    // the thread is woken up, check whether buffer closed
    if (already_closed(buffer)) return CLOSED_ERROR;
  }

/// We separate size and "a" (occupied) from allocator.
static block_info unpack(word_t word) {
  block_info info;
  info.occupied = word & 1;
  info.size = info.occupied ? word - 1:word;
  return info;
}

    if (already_closed(buffer)) return CLOSED_ERROR;
  }

void simulate(char *dp)
{
		iki_schedule_processes_at_time_zero(dp, "xsim.dir/tb_behav/xsim.reloc");
	// Initialize Verilog nets in mixed simulation, for the cases when the value at time 0 should be propagated from the mixed language Vhdl net
	iki_execute_processes();

int mdadm_unmount(void) {
  monad_apply(from_command(JBOD_UNMOUNT), NULL);
  return 1;
}

#include <stdlib.h>
#include <string.h>
#include <stdio.h>

int mdadm_write(uint32_t addr, uint32_t len, const uint8_t *buf) {
  // printf("addr = %u, len = %u\n", addr, len);
  if (addr < 0 || addr + len > 1048576 || len > 1024) return -1;
  if (!len) return len;
  if (!buf) return -1;

#define unpack(cmd) cmd.disk_id, cmd.block_id
void cached_write(const uint8_t *buf, JBOD cmd) {
  if (!cache_enabled()) return;
  if (cache_insert(unpack(cmd), buf) == -1)
    cache_update(unpack(cmd), buf);
}

// Takes an array of integers and the length of the array as input and double every positive element of the array that is an Armstrong number.
void double_armstrongs(int array[], int length) {
	int i;
	for (i = 0; i < length; ++i) if (is_arm(array[i])) array[i] = 2 * (array[i]);
}

int seek(JBOD cmd) {
  cmd.command = JBOD_SEEK_TO_DISK;
  monad_apply(cmd, NULL);
  cmd.command = JBOD_SEEK_TO_BLOCK;
  monad_apply(cmd, NULL);
  return 0;
}

#include "iki.h"
#include <string.h>
#include <math.h>
#ifdef __GNUC__
#include <stdlib.h>
#else
#include <malloc.h>
#define alloca _alloca
#endif
typedef void (*funcp)(char *, char *);
extern int main(int, char**);
extern void execute_2(char*, char *);
extern void execute_25(char*, char *);
extern void execute_54(char*, char *);
extern void execute_31(char*, char *);
extern void execute_32(char*, char *);
extern void execute_33(char*, char *);
extern void execute_34(char*, char *);
extern void execute_35(char*, char *);
extern void execute_36(char*, char *);
extern void execute_37(char*, char *);
extern void execute_38(char*, char *);
extern void execute_39(char*, char *);
extern void execute_40(char*, char *);
extern void execute_41(char*, char *);
extern void execute_42(char*, char *);
extern void execute_43(char*, char *);
extern void execute_44(char*, char *);
extern void execute_45(char*, char *);
extern void execute_46(char*, char *);
extern void execute_47(char*, char *);
extern void execute_48(char*, char *);
extern void execute_49(char*, char *);
extern void execute_50(char*, char *);
extern void execute_51(char*, char *);
extern void execute_52(char*, char *);
extern void execute_53(char*, char *);
extern void execute_5(char*, char *);
extern void execute_7(char*, char *);
extern void execute_8(char*, char *);
extern void execute_10(char*, char *);
extern void execute_11(char*, char *);
extern void execute_13(char*, char *);
extern void execute_15(char*, char *);
extern void execute_17(char*, char *);
extern void execute_19(char*, char *);
extern void execute_20(char*, char *);
extern void execute_22(char*, char *);
extern void execute_30(char*, char *);
extern void execute_24(char*, char *);
extern void execute_27(char*, char *);
extern void execute_28(char*, char *);
extern void execute_29(char*, char *);
extern void execute_55(char*, char *);
extern void execute_56(char*, char *);
extern void execute_57(char*, char *);
extern void execute_58(char*, char *);
extern void execute_59(char*, char *);
extern void vlog_transfunc_eventcallback(char*, char*, unsigned, unsigned, unsigned, char *);
funcp funcTab[48] = {(funcp)execute_2, (funcp)execute_25, (funcp)execute_54, (funcp)execute_31, (funcp)execute_32, (funcp)execute_33, (funcp)execute_34, (funcp)execute_35, (funcp)execute_36, (funcp)execute_37, (funcp)execute_38, (funcp)execute_39, (funcp)execute_40, (funcp)execute_41, (funcp)execute_42, (funcp)execute_43, (funcp)execute_44, (funcp)execute_45, (funcp)execute_46, (funcp)execute_47, (funcp)execute_48, (funcp)execute_49, (funcp)execute_50, (funcp)execute_51, (funcp)execute_52, (funcp)execute_53, (funcp)execute_5, (funcp)execute_7, (funcp)execute_8, (funcp)execute_10, (funcp)execute_11, (funcp)execute_13, (funcp)execute_15, (funcp)execute_17, (funcp)execute_19, (funcp)execute_20, (funcp)execute_22, (funcp)execute_30, (funcp)execute_24, (funcp)execute_27, (funcp)execute_28, (funcp)execute_29, (funcp)execute_55, (funcp)execute_56, (funcp)execute_57, (funcp)execute_58, (funcp)execute_59, (funcp)vlog_transfunc_eventcallback};
const int NumRelocateId= 48;

/**
 * mm_checkheap
 * Validates a heap.
 */
bool mm_checkheap(int lineno) {
  if (!heap_data) return true;
  return !(check_free_blocks(lineno) || check_heap(lineno));
}

/// Modify the pointer to the next block.
inline static void modify_next(word_t *base_addr, const word_t *pointed_addr) {
  *(base_addr + 1) = (word_t) pointed_addr;
}

#define apply_data(i, buf) \
  memcpy(cache[i].block, buf, JBOD_BLOCK_SIZE); \
  cache[i].access_time = clock++; \
  cache[i].valid = true; \
  cache[i].disk_num = disk_num; \
  cache[i].block_num = block_num;

  uint8_t cache[JBOD_BLOCK_SIZE];
  uint32_t write_len = len;
  while (write_len > 0) {
    if (block_offset > 0 || write_len < JBOD_BLOCK_SIZE) {
      if (cached_read(cache, cmd, false)) return -1;
      if (seek(cmd)) return -1;
    }
    uint32_t current_write_len = write_len > JBOD_BLOCK_SIZE ? JBOD_BLOCK_SIZE : write_len;
    if (block_offset > 0) {
      uint32_t max_can_read = JBOD_BLOCK_SIZE - block_offset;
      if (max_can_read < current_write_len) current_write_len = max_can_read;
      memcpy(cache + block_offset, buf, current_write_len);
      block_offset = 0;
    } else memcpy(cache, buf, current_write_len);
    monad_apply(from_command(JBOD_WRITE_BLOCK), cache);
    cached_write(cache, cmd);
    buf += current_write_len;
    write_len -= current_write_len;
    if (inc_block(&cmd)) return -1;
  }
  return len;
}

#include "iki.h"
#include <string.h>
#include <math.h>
#ifdef __GNUC__
#include <stdlib.h>
#else
#include <malloc.h>
#define alloca _alloca
#endif
typedef void (*funcp)(char *, char *);
extern int main(int, char**);
extern void execute_4(char*, char *);
extern void execute_5(char*, char *);
extern void execute_14(char*, char *);
extern void execute_15(char*, char *);
extern void execute_16(char*, char *);
extern void execute_17(char*, char *);
extern void execute_18(char*, char *);
extern void execute_19(char*, char *);
extern void execute_20(char*, char *);
extern void execute_21(char*, char *);
extern void execute_3(char*, char *);
extern void vlog_simple_process_execute_0_fast_no_reg_no_agg(char*, char*, char*);
extern void execute_12(char*, char *);
extern void execute_13(char*, char *);
extern void execute_7(char*, char *);
extern void execute_8(char*, char *);
extern void execute_9(char*, char *);
extern void execute_22(char*, char *);
extern void execute_23(char*, char *);
extern void execute_24(char*, char *);
extern void execute_25(char*, char *);
extern void execute_26(char*, char *);
extern void vlog_transfunc_eventcallback(char*, char*, unsigned, unsigned, unsigned, char *);
funcp funcTab[23] = {(funcp)execute_4, (funcp)execute_5, (funcp)execute_14, (funcp)execute_15, (funcp)execute_16, (funcp)execute_17, (funcp)execute_18, (funcp)execute_19, (funcp)execute_20, (funcp)execute_21, (funcp)execute_3, (funcp)vlog_simple_process_execute_0_fast_no_reg_no_agg, (funcp)execute_12, (funcp)execute_13, (funcp)execute_7, (funcp)execute_8, (funcp)execute_9, (funcp)execute_22, (funcp)execute_23, (funcp)execute_24, (funcp)execute_25, (funcp)execute_26, (funcp)vlog_transfunc_eventcallback};
const int NumRelocateId= 23;

#include "mm.h"
#include "memlib.h"

void relocate(char *dp)
{
	iki_relocate(dp, "xsim.dir/tb_behav/xsim.reloc",  (void **)funcTab, 66);

/*
 * mm.c
 *
 * NAMES:
 *
 * The whole file is written by Zihui Xie, , and Yuanxiang Wang.
 * The whole project realizes functions such as malloc, free, realloc, calloc, and memalign.
 * The project also includes a function to print the heap.
 * We debug based on checkpoint files and gdb commands.
 * Implementation method:
 *  + Data structure: implicit list of blocks + explicit free list
    + Alignment: 16 bytes, or 2 words
    + Coalesces adjacent free blocks
    + Check heap function validates the linked list and the consecutive-ness of the blocks
    + Malloc splits block if the available block is very large, using a first-fit strategy
 */

#include "iki.h"
#include <string.h>
#include <math.h>
#ifdef __GNUC__
#include <stdlib.h>
#else
#include <malloc.h>
#define alloca _alloca
#endif
typedef void (*funcp)(char *, char *);
extern int main(int, char**);
extern void execute_2(char*, char *);
extern void vlog_simple_process_execute_0_fast_no_reg_no_agg(char*, char*, char*);
extern void execute_9(char*, char *);
extern void execute_10(char*, char *);
extern void execute_4(char*, char *);
extern void execute_5(char*, char *);
extern void execute_6(char*, char *);
extern void execute_11(char*, char *);
extern void execute_12(char*, char *);
extern void execute_13(char*, char *);
extern void execute_14(char*, char *);
extern void execute_15(char*, char *);
extern void vlog_transfunc_eventcallback(char*, char*, unsigned, unsigned, unsigned, char *);
funcp funcTab[13] = {(funcp)execute_2, (funcp)vlog_simple_process_execute_0_fast_no_reg_no_agg, (funcp)execute_9, (funcp)execute_10, (funcp)execute_4, (funcp)execute_5, (funcp)execute_6, (funcp)execute_11, (funcp)execute_12, (funcp)execute_13, (funcp)execute_14, (funcp)execute_15, (funcp)vlog_transfunc_eventcallback};
const int NumRelocateId= 13;

/// Check the return value of sbrk
static bool is_sbrk_invalid(void *ptr) {
  return ptr == (void *) -1;
}

/**********************************************************************/
/*   ____  ____                                                       */
/*  /   /\/   /                                                       */
/* /___/  \  /                                                        */
/* \   \   \/                                                         */
/*  \   \        Copyright (c) 2003-2013 Xilinx, Inc.                 */
/*  /   /        All Right Reserved.                                  */
/* /---/   /\                                                         */
/* \   \  /  \                                                        */
/*  \___\/\___\                                                       */
/**********************************************************************/

void simulate(char *dp)
{
		iki_schedule_processes_at_time_zero(dp, "xsim.dir/testbench_behav/xsim.reloc");
	// Initialize Verilog nets in mixed simulation, for the cases when the value at time 0 should be propagated from the mixed language Vhdl net
	iki_execute_processes();

int main(int argc, char **argv)
{
    iki_heap_initialize("ms", "isimmm", 0, 2147483648) ;
    iki_set_sv_type_file_path_name("xsim.dir/test_bench_behav/xsim.svtype");
    iki_set_crvs_dump_file_path_name("xsim.dir/test_bench_behav/xsim.crvsdump");
    void* design_handle = iki_create_design("xsim.dir/test_bench_behav/xsim.mem", (void *)relocate, (void *)sensitize, (void *)simulate, 0, isimBridge_getWdbWriter(), 0, argc, argv);
     iki_set_rc_trial_count(100);
    (void) design_handle;
    return iki_simulate_design();
}


/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#define memset mem_memset
#define memcpy mem_memcpy
#endif /* DRIVER */

/// As the name suggests :)
/// Assumes: ptr is already in the free list
static word_t *free_and_coalesce(word_t *ptr, word_t size) {
  heap_data->free_block_count++;
  word_t *ptr_prev = ptr > heap_data->first_block ? ptr - information(ptr - 1).size : NULL;
  word_t *ptr_next = ptr < heap_data->last_block ? ptr + size : NULL;
  word_t prev_size = release_free_block(ptr_prev);
  // What is the size of the coalesced block?
  word_t new_size = size + prev_size + release_free_block(ptr_next);
  // What is the starting address of the coalesced block?
  word_t *base_addr = prev_size > 0 ? ptr_prev : ptr;
  if (DEBUG && new_size != size) {
    printf("Coalesce: at %p -> %p, size %lu -> %lu\n", ptr, base_addr, size, new_size);
  }
  // Refresh the size information
  modify_size_info(base_addr, new_size, false);
  // Add the new block to the head
  if (base_addr != heap_data->head)
    insert_before(base_addr, heap_data->head);
  // The "prev" of the new head is NULL, of course
  modify_prev(base_addr, NULL);
  return base_addr;
}

extern SYSTEMCLIB_IMP_DLLSPEC int xsim_argc_copy ;
extern SYSTEMCLIB_IMP_DLLSPEC char** xsim_argv_copy ;

#include "iki.h"
#include <string.h>
#include <math.h>
#ifdef __GNUC__
#include <stdlib.h>
#else
#include <malloc.h>
#define alloca _alloca
#endif
typedef void (*funcp)(char *, char *);
extern int main(int, char**);
extern void execute_2(char*, char *);
extern void execute_33(char*, char *);
extern void execute_76(char*, char *);
extern void execute_39(char*, char *);
extern void execute_40(char*, char *);
extern void execute_41(char*, char *);
extern void execute_42(char*, char *);
extern void execute_43(char*, char *);
extern void execute_44(char*, char *);
extern void execute_45(char*, char *);
extern void execute_46(char*, char *);
extern void execute_47(char*, char *);
extern void execute_48(char*, char *);
extern void execute_49(char*, char *);
extern void execute_50(char*, char *);
extern void execute_51(char*, char *);
extern void execute_52(char*, char *);
extern void execute_53(char*, char *);
extern void execute_54(char*, char *);
extern void execute_55(char*, char *);
extern void execute_56(char*, char *);
extern void execute_57(char*, char *);
extern void execute_58(char*, char *);
extern void execute_59(char*, char *);
extern void execute_60(char*, char *);
extern void execute_61(char*, char *);
extern void execute_62(char*, char *);
extern void execute_63(char*, char *);
extern void execute_64(char*, char *);
extern void execute_65(char*, char *);
extern void execute_66(char*, char *);
extern void execute_67(char*, char *);
extern void execute_68(char*, char *);
extern void execute_69(char*, char *);
extern void execute_70(char*, char *);
extern void execute_71(char*, char *);
extern void execute_72(char*, char *);
extern void execute_73(char*, char *);
extern void execute_74(char*, char *);
extern void execute_75(char*, char *);
extern void execute_5(char*, char *);
extern void execute_7(char*, char *);
extern void execute_8(char*, char *);
extern void execute_10(char*, char *);
extern void execute_11(char*, char *);
extern void execute_13(char*, char *);
extern void execute_15(char*, char *);
extern void execute_17(char*, char *);
extern void execute_19(char*, char *);
extern void execute_20(char*, char *);
extern void execute_22(char*, char *);
extern void execute_38(char*, char *);
extern void execute_24(char*, char *);
extern void execute_26(char*, char *);
extern void execute_28(char*, char *);
extern void execute_30(char*, char *);
extern void execute_32(char*, char *);
extern void execute_35(char*, char *);
extern void execute_36(char*, char *);
extern void execute_37(char*, char *);
extern void execute_77(char*, char *);
extern void execute_78(char*, char *);
extern void execute_79(char*, char *);
extern void execute_80(char*, char *);
extern void execute_81(char*, char *);
extern void vlog_transfunc_eventcallback(char*, char*, unsigned, unsigned, unsigned, char *);
funcp funcTab[66] = {(funcp)execute_2, (funcp)execute_33, (funcp)execute_76, (funcp)execute_39, (funcp)execute_40, (funcp)execute_41, (funcp)execute_42, (funcp)execute_43, (funcp)execute_44, (funcp)execute_45, (funcp)execute_46, (funcp)execute_47, (funcp)execute_48, (funcp)execute_49, (funcp)execute_50, (funcp)execute_51, (funcp)execute_52, (funcp)execute_53, (funcp)execute_54, (funcp)execute_55, (funcp)execute_56, (funcp)execute_57, (funcp)execute_58, (funcp)execute_59, (funcp)execute_60, (funcp)execute_61, (funcp)execute_62, (funcp)execute_63, (funcp)execute_64, (funcp)execute_65, (funcp)execute_66, (funcp)execute_67, (funcp)execute_68, (funcp)execute_69, (funcp)execute_70, (funcp)execute_71, (funcp)execute_72, (funcp)execute_73, (funcp)execute_74, (funcp)execute_75, (funcp)execute_5, (funcp)execute_7, (funcp)execute_8, (funcp)execute_10, (funcp)execute_11, (funcp)execute_13, (funcp)execute_15, (funcp)execute_17, (funcp)execute_19, (funcp)execute_20, (funcp)execute_22, (funcp)execute_38, (funcp)execute_24, (funcp)execute_26, (funcp)execute_28, (funcp)execute_30, (funcp)execute_32, (funcp)execute_35, (funcp)execute_36, (funcp)execute_37, (funcp)execute_77, (funcp)execute_78, (funcp)execute_79, (funcp)execute_80, (funcp)execute_81, (funcp)vlog_transfunc_eventcallback};
const int NumRelocateId= 66;

  return BUFFER_SUCCESS;

/* Lab- 1 Due by 11th Feb 2022
   Make sure your code looks clean
   Write comments with your code
   Do not foget to 'push' your code github reglarly
   */

  JBOD cmd = compute_cmd(addr, len);
  uint32_t block_offset = addr % JBOD_BLOCK_SIZE;
  if (seek(cmd)) return -1;

/**
 * free
 */
void free(void *ptr) {
  word_t *base_addr = ((word_t *) ptr) - 1;
  block_info info = information(base_addr);
  if (DEBUG) printf("Free: base_addr = %p, size = %zu, occ = %i\n", base_addr, info.size, info.occupied);
  free_and_coalesce(base_addr, info.size);
}

// const size_t LARGE_UNIT = 2048;
/// In case size==0, we grow by a default size.
/// Assume the unit of size is word.
static word_t *grow_heap(size_t words) {
  // If the last block is free, we may request a
  // smaller block and coalease to get an appropriate block
  if (heap_data->last_block) {
    block_info info = information(heap_data->last_block);
    if (!info.occupied && info.size < words) {
      words -= info.size;
    }
  }
  // How many bytes to sbrk when the heapsize is not enough?
  if (words <= heap_data->alloc_unit) words = heap_data->alloc_unit;
  // if (heap_data->alloc_unit == (1 << 15)) heap_data->alloc_unit = 1 << 14;
  // else if (words <= LARGE_UNIT) words = LARGE_UNIT;
  // else: words = words
  if (DEBUG) printf("Grow: words = %zu\n", words);
  word_t *ptr = mem_sbrk((intptr_t) (words * sizeof(word_t)));
  if (is_sbrk_invalid(ptr)) return NULL;
  heap_data->last_block = ptr;
  return free_and_coalesce(ptr, words);
}

static cache_entry_t *cache = NULL;
static int cache_size = 0;
static int clock = 0;
static int num_queries = 0;
static int num_hits = 0;

#endif


/* attempts to connect to server and set the global cli_sd variable to the
 * socket; returns true if successful and false if not. 
 * this function will be invoked by tester to connect to the server at given ip and port.
 * you will not call it in mdadm.c
*/
bool jbod_connect(const char *ip, uint16_t port) {
  cli_sd = socket(AF_INET, SOCK_STREAM, 0);
  if (cli_sd < 0) return false;
  struct sockaddr_in serv_addr;
  serv_addr.sin_family = AF_INET;
  serv_addr.sin_port = htons(port);
  if (!inet_aton(ip, &serv_addr.sin_addr))
    return false;
  return !connect(cli_sd, (const struct sockaddr *) &serv_addr, sizeof(serv_addr));
}

void sensitize(char *dp)
{
	iki_sensitize(dp, "xsim.dir/tb_behav/xsim.reloc");
}

void sensitize(char *dp)
{
	iki_sensitize(dp, "xsim.dir/testbench_behav/xsim.reloc");
}

// Takes pointers to two integers and swaps the values of integers
void swap(int *a, int *b) {
	// The obvious implementation
	int t = *a;
	*a = *b;
	*b = t;
}

#include "iki.h"
#include <string.h>
#include <math.h>
#ifdef __GNUC__
#include <stdlib.h>
#else
#include <malloc.h>
#define alloca _alloca
#endif
typedef void (*funcp)(char *, char *);
extern int main(int, char**);
extern void execute_2(char*, char *);
extern void execute_35(char*, char *);
extern void execute_79(char*, char *);
extern void execute_41(char*, char *);
extern void execute_42(char*, char *);
extern void execute_43(char*, char *);
extern void execute_44(char*, char *);
extern void execute_45(char*, char *);
extern void execute_46(char*, char *);
extern void execute_47(char*, char *);
extern void execute_48(char*, char *);
extern void execute_49(char*, char *);
extern void execute_50(char*, char *);
extern void execute_51(char*, char *);
extern void execute_52(char*, char *);
extern void execute_53(char*, char *);
extern void execute_54(char*, char *);
extern void execute_55(char*, char *);
extern void execute_56(char*, char *);
extern void execute_57(char*, char *);
extern void execute_58(char*, char *);
extern void execute_59(char*, char *);
extern void execute_60(char*, char *);
extern void execute_61(char*, char *);
extern void execute_62(char*, char *);
extern void execute_63(char*, char *);
extern void execute_64(char*, char *);
extern void execute_65(char*, char *);
extern void execute_66(char*, char *);
extern void execute_67(char*, char *);
extern void execute_68(char*, char *);
extern void execute_69(char*, char *);
extern void execute_70(char*, char *);
extern void execute_71(char*, char *);
extern void execute_72(char*, char *);
extern void execute_73(char*, char *);
extern void execute_74(char*, char *);
extern void execute_75(char*, char *);
extern void execute_76(char*, char *);
extern void execute_77(char*, char *);
extern void execute_78(char*, char *);
extern void execute_5(char*, char *);
extern void execute_7(char*, char *);
extern void execute_8(char*, char *);
extern void execute_10(char*, char *);
extern void execute_11(char*, char *);
extern void execute_13(char*, char *);
extern void execute_15(char*, char *);
extern void execute_17(char*, char *);
extern void execute_19(char*, char *);
extern void execute_20(char*, char *);
extern void execute_22(char*, char *);
extern void execute_24(char*, char *);
extern void execute_40(char*, char *);
extern void execute_26(char*, char *);
extern void execute_28(char*, char *);
extern void execute_30(char*, char *);
extern void execute_32(char*, char *);
extern void execute_34(char*, char *);
extern void execute_37(char*, char *);
extern void execute_38(char*, char *);
extern void execute_39(char*, char *);
extern void execute_80(char*, char *);
extern void execute_81(char*, char *);
extern void execute_82(char*, char *);
extern void execute_83(char*, char *);
extern void execute_84(char*, char *);
extern void vlog_transfunc_eventcallback(char*, char*, unsigned, unsigned, unsigned, char *);
funcp funcTab[68] = {(funcp)execute_2, (funcp)execute_35, (funcp)execute_79, (funcp)execute_41, (funcp)execute_42, (funcp)execute_43, (funcp)execute_44, (funcp)execute_45, (funcp)execute_46, (funcp)execute_47, (funcp)execute_48, (funcp)execute_49, (funcp)execute_50, (funcp)execute_51, (funcp)execute_52, (funcp)execute_53, (funcp)execute_54, (funcp)execute_55, (funcp)execute_56, (funcp)execute_57, (funcp)execute_58, (funcp)execute_59, (funcp)execute_60, (funcp)execute_61, (funcp)execute_62, (funcp)execute_63, (funcp)execute_64, (funcp)execute_65, (funcp)execute_66, (funcp)execute_67, (funcp)execute_68, (funcp)execute_69, (funcp)execute_70, (funcp)execute_71, (funcp)execute_72, (funcp)execute_73, (funcp)execute_74, (funcp)execute_75, (funcp)execute_76, (funcp)execute_77, (funcp)execute_78, (funcp)execute_5, (funcp)execute_7, (funcp)execute_8, (funcp)execute_10, (funcp)execute_11, (funcp)execute_13, (funcp)execute_15, (funcp)execute_17, (funcp)execute_19, (funcp)execute_20, (funcp)execute_22, (funcp)execute_24, (funcp)execute_40, (funcp)execute_26, (funcp)execute_28, (funcp)execute_30, (funcp)execute_32, (funcp)execute_34, (funcp)execute_37, (funcp)execute_38, (funcp)execute_39, (funcp)execute_80, (funcp)execute_81, (funcp)execute_82, (funcp)execute_83, (funcp)execute_84, (funcp)vlog_transfunc_eventcallback};
const int NumRelocateId= 68;

/// Returns the address of the previous block.
static word_t *prev_block(const word_t *base_addr) {
  return *(word_t **) (base_addr + 2);
}

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <stdbool.h>
#include <stdint.h>

/** What is the correct alignment? */
const size_t ALIGNMENT = 16;
typedef uint64_t word_t;
/// Size of two words, at the beginning and the end of the block.
const size_t INFO_SIZE = 2;
/// Size of an empty block.
const size_t MIN_BLOCK_SIZE = 4;
const bool DEBUG = false;

// Closes the buffer and informs all the blocking send/receive/select calls to return with CLOSED_ERROR
// Once the buffer is closed, send/receive/select operations will cease to function and just return CLOSED_ERROR
// Returns BUFFER_SUCCESS if close is successful,
// CLOSED_ERROR if the buffer is already closed, and
// BUFFER_ERROR in any other error case
enum buffer_status buffer_close(state_t *buffer) {

  // receive messages
  if (BUFFER_SUCCESS == (status = buffer_remove_Q(buffer, data))) {
    // check whether is special message
    if (strcmp((const char *) data, "splmsg") == 0) {
      puts("Special message. What?");
      status = BUFFER_SPECIAL_MESSSAGE;
    }

/// A reconstruction of uint32_t that fits our need
typedef struct {
  uint32_t block_id : 8;
  uint32_t reserved : 14;
  uint32_t disk_id : 4;
  jbod_cmd_t command : 6;
} JBOD;

#include "mdadm.h"
#include "jbod.h"
#include "net.h"

/// Remove the block from linked list when necessary
/// Returns: the released block size,
///  positive if ptr != null and it is free
///  0 if ptr == null or it is occupied
static word_t release_free_block(word_t *ptr) {
  if (!ptr) return 0;
  block_info info = information(ptr);
  if (!info.occupied) {
    remove_block(ptr);
    return info.size;
  }
  return 0;
}

// Power helpers
int sq(int i) { return i * i; }
int cb(int i) { return i * i * i; }
int pwr(int n, int i) { return i ? n * pwr(n, i - 1) : 1; }

#define for_caches(i) \
  int i;              \
  for (i = 0; i < cache_size; ++i)
#define block_matches(i) \
  cache[i].valid && cache[i].block_num == block_num &&cache[i].disk_num == disk_num

// Creates a buffer with the given capacity
state_t *buffer_create(int capacity) {
  state_t *buffer = (state_t *) malloc(sizeof(state_t));
  buffer->fifoQ = (fifo_t *) malloc(sizeof(fifo_t));
  fifo_init(buffer->fifoQ, capacity);
  buffer->isopen = true;
  if (pthread_mutex_init(&buffer->chclose, NULL)
      && pthread_cond_init(&buffer->chconsend, NULL)
      && pthread_mutex_init(&buffer->chmutex, NULL)
      && pthread_cond_init(&buffer->chconrec, NULL) != 0) {
    puts("Failed to initialize buffer");
    // Don't expect this to happen
  }
  return buffer;
}

  // wake up all threads and close them
  run_both(pthread_cond_broadcast, &buffer->chconsend, &buffer->chconrec);
  run_both(pthread_mutex_unlock, &buffer->chmutex, &buffer->chclose);

/// A monadic syntax for applying a command
#define monad_apply(cmd, buf) { if (apply_cmd(cmd, buf)) return -1; }

void simulate(char *dp)
{
		iki_schedule_processes_at_time_zero(dp, "xsim.dir/test_bench_behav/xsim.reloc");
	// Initialize Verilog nets in mixed simulation, for the cases when the value at time 0 should be propagated from the mixed language Vhdl net
	iki_execute_processes();

  pthread_mutex_lock(&buffer->chmutex);

int main(int argc, char **argv)
{
    iki_heap_initialize("ms", "isimmm", 0, 2147483648) ;
    iki_set_sv_type_file_path_name("xsim.dir/main_behav/xsim.svtype");
    iki_set_crvs_dump_file_path_name("xsim.dir/main_behav/xsim.crvsdump");
    void* design_handle = iki_create_design("xsim.dir/main_behav/xsim.mem", (void *)relocate, (void *)sensitize, (void *)simulate, 0, isimBridge_getWdbWriter(), 0, argc, argv);
     iki_set_rc_trial_count(100);
    (void) design_handle;
    return iki_simulate_design();
}


  return status;
}
// test_send_correctness 1
// Reads data from the given buffer and stores it in the function’s input parameter, data (Note that it is a double pointer).
// This is a blocking call i.e., the function only returns on a successful completion of receive
// In case the buffer is empty, the function waits till the buffer has some data to read
// Return BUFFER_SPECIAL_MESSSAGE for successful retrieval of special data "splmsg"
// Returns BUFFER_SUCCESS for successful retrieval of any data other than "splmsg"
// CLOSED_ERROR if the buffer is closed, and
// BUFFER_ERROR on encountering any other generic error of any sort

int is_arm(int n) {
	if (n <= 0) return 0;
	int all = 0, m = n, pw = 0;
	// Calculate pw: the number of digits in n
	while (m) { ++pw; m /= 10; }
	m = n;
	while (n > 0) {
		// Sum up
		all += pwr(n % 10, pw);
		n /= 10;
	}
	// Is it armstrong?
	return all == m;
}

cache_entry_t *find_cache(int disk_num, int block_num) {
  for_caches(i) {
    if (block_matches(i))
      return &cache[i];
  }
  return NULL;
}

#include <stdbool.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <stdio.h>
#include <errno.h>
#include <err.h>
#include <sys/socket.h>
#include <sys/types.h>
#include <arpa/inet.h>
#include "net.h"
#include "jbod.h"
// #include <assert.h>
// static_assert(sizeof(MsgHead) == HEADER_LEN);

//Takes an array of integers and the length of the array as input and cubes  every prime element of the array
void cube_primes(int array[], int length) {
	int i;
	for (i = 0; i < length; ++i) if (is_prime(array[i])) array[i] = cb(array[i]);
}

/**
 * calloc
 * This function is not tested by mdriver, and has been implemented for you.
 */
void *calloc(size_t nmemb, size_t size) {
  void *ptr;
  size *= nmemb;
  ptr = malloc(size);
  if (ptr) {
    memset(ptr, 0, size);
  }
  return ptr;
}

/// Modify the size information of a block.
static void modify_size_info(word_t *base_addr, word_t size, bool occupied) {
  word_t packed_data = size | (occupied ? 1:0);
  *base_addr = packed_data;
  *(base_addr + size - 1) = packed_data;
}

#ifndef __JBOD_STRUCT_ONLY__

int is_happy(int n) {
	// Reference: https://en.wikipedia.org/wiki/Happy_number#10-happy_numbers
	if (n < 10) return n == 1 || n == 7;
	// For one digit numbers, only 1 and 7 are happy
	int all = 0;
	while (n > 0) {
		all += sq(n % 10);
		n /= 10;
	}
	// Recursively test until n < 10
	return is_happy(all);
}

}
#include "iki_bridge.h"
void relocate(char *);

#include "student.h"
#include <stdbool.h>

void relocate(char *dp)
{
	iki_relocate(dp, "xsim.dir/tb_behav/xsim.reloc",  (void **)funcTab, 68);

//Take an array of integers and length of the arrays as input and negate every happy number of that array
void negate_happy(int array[], int length) {
	int i;
	for (i = 0; i < length; ++i) if (is_happy(array[i])) array[i] = -(array[i]);
}


/// The most complex logic
int mdadm_read(uint32_t addr, uint32_t len, uint8_t *buf) {
  if (addr < 0 || addr + len > 1048576 || len > 1024) return -1;
  if (!len) return len;
  if (!buf) return -1;

enum buffer_status buffer_destroy(state_t *buffer) {
  if (buffer->isopen) {
    return DESTROY_ERROR;
  }
  if (run_both(pthread_mutex_destroy, &buffer->chclose, &buffer->chmutex)
      && run_both(pthread_cond_destroy, &buffer->chconsend, &buffer->chconrec)
      != 0)
    puts("Failed to destroy buffer");
  fifo_free(buffer->fifoQ);
  free(buffer);
  return BUFFER_SUCCESS;
}
