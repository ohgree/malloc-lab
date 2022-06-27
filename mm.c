/*
 * mm.c - Malloc package using ordered, explicitly linked, segregated free lists
 *        with a few heuristics for reallocation.
 *
 * Every block has a 4 byte header and footer. Header and footer both contains
 * size (word-aligned 32 bits), allocation info (LSB). Only the header has an
 * additional tag for reallocation related info (second to last bit).
 *
 * Free blocks are stored in linked lists which are segregated by block sizes,
 * and are sorted by memory address in ascending order. n-th list contains
 * blocks with size in range [2^n, 2^(n+1)).
 *
 * Every free and heap extension immediately performs coalescing.
 *
 * Reallocation uses buffer to reallocate block in-place and reallocation bit is
 * used to handle future block expansion as well as possible.
 *
 * Header entries consist of the block size (all 32 bits), reallocation tag
 * (second-last bit), and allocation bit (last bit).
 *
 * MJ Shin
 *
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "memlib.h"
#include "mm.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your information in the following struct.
 ********************************************************/
team_t team = {
    /* Your student ID */
    "20161603",
    /* Your full name*/
    "Minjun Shin",
    /* Your email address */
    "ohgree.dev@gmail.com",
};

/*
 * Constants
 */
#define WORD_SIZE 4
#define DWORD_SIZE 8
#define PAGE_SIZE (1 << 12)
#define MIN_SIZE 16

#define SEGREGATED_LISTS 20
#define REALLOCATION_BUFFER (1 << 7)

/*
 * Macros
 */
#define MIN(x, y) ((x) < (y) ? (x) : (y))
#define MAX(x, y) ((x) > (y) ? (x) : (y))

// pack size and allocation bits into a word
#define PACK(size, allocated) ((size) | (allocated))

// read and write a word at p
#define GET(p) (*(size_t *)(p))

// read the size and allocation bit from address p
#define GET_SIZE(p) (GET(p) & ~0x7)     // Mask 0b11111000 (Bit 3-7)
#define GET_TAG(p) (GET(p) & 0x2)       // Mask 0b00000010 (Bit 1)
#define GET_ALLOCATED(p) (GET(p) & 0x1) // Mask 0b00000001 (LSB)

// put value while preserving reallocation bit
#define PUT(p, val) (*(size_t *)(p) = (val) | GET_TAG(p))
// put value while clearing reallocation bit
#define PUT_CLEAN(p, val) (*(size_t *)(p) = (val))

// store predecessor or successor pointer for free blocks
#define SET_PTR(p, ptr) (*(size_t *)(p) = (size_t)(ptr))

// modify reallocation tag
#define SET_TAG(p) (*(size_t *)(p) = GET(p) | 0x2)    // Set bit 1
#define UNSET_TAG(p) (*(size_t *)(p) = GET(p) & ~0x2) // Unset bit 1

// block's header and footer address
#define HEADER(ptr) ((char *)(ptr)-WORD_SIZE)
#define FOOTER(ptr) ((char *)(ptr) + GET_SIZE(HEADER(ptr)) - DWORD_SIZE)

// next & previous block address
#define NEXT(ptr) ((char *)(ptr) + GET_SIZE((char *)(ptr)-WORD_SIZE))
#define PREV(ptr) ((char *)(ptr)-GET_SIZE((char *)(ptr)-DWORD_SIZE))

// address of free block's predecessor and successor
#define PRED_PTR(ptr) ((char *)(ptr))
#define SUCC_PTR(ptr) ((char *)(ptr) + WORD_SIZE)

// address of predecessor and successor in the segregated free list
#define PRED(ptr) (*(char **)(ptr))
#define SUCC(ptr) (*(char **)(SUCC_PTR(ptr)))

/*
 * Globals
 */
void **free_lists; /* Array of segregated free lists */

/*
 * Function prototypes
 */
static void *extend_heap(size_t bytes);
static void *coalesce(void *ptr);
static void *place(void *ptr, size_t asize);
static void insert_item(void *item, size_t size);
static void delete_item(void *ptr);

/**
 * @brief Initialize malloc package.
 * Constructs prologue & epilogue blocks to mark the start and end of heap
 * accordingly.
 *
 * @return int value 0 on success, -1 on error.
 */
int mm_init(void) {
  char *heap_base; // Pointer to beginning of heap
  void *free_list_base;

  // allocate segregated lists array and initial empty heap
  if ((ssize_t)(free_list_base =
                    mem_sbrk((SEGREGATED_LISTS + 4) * WORD_SIZE)) == -1) {
    return -1;
  }

  free_lists = free_list_base;
  heap_base = free_list_base + SEGREGATED_LISTS * WORD_SIZE;

  // padding for DWORD alignment
  PUT_CLEAN(heap_base, 0);

  // prologue block header & footer
  PUT_CLEAN(heap_base + WORD_SIZE, PACK(DWORD_SIZE, 1));
  PUT_CLEAN(heap_base + (WORD_SIZE * 2), PACK(DWORD_SIZE, 1));

  // epilogue block header
  PUT_CLEAN(heap_base + (WORD_SIZE * 3), PACK(0, 1));

  // initialize segregated free lists to NULLs
  for (int i = 0; i < SEGREGATED_LISTS; i++) {
    free_lists[i] = NULL;
  }

  if (!extend_heap(PAGE_SIZE)) {
    return -1;
  }

  return 0;
}

/**
 * @brief Allocate a block with @p size.
 * Extends heap if necessary. The blocks are padded with boundary tags and are
 * dword-aligned.
 *
 * @param size Size in bytes
 * @return void* Pointer to allocated memory block
 */
void *mm_malloc(size_t size) {
  size_t asize;
  void *ptr = NULL;

  if (size == 0) {
    // ignore when asked for zero-size
    return NULL;
  }

  // adjust block size
  if (size > DWORD_SIZE) {
    asize = (size + DWORD_SIZE + (DWORD_SIZE - 1)) & ~0x7;
  } else {
    // if no more than one dword was requested
    asize = DWORD_SIZE * 2;
  }

  // choose a free block from segregated list with enough size
  size_t search_size = asize;
  for (int list = 0; list < SEGREGATED_LISTS; list++) {
    if ((list == SEGREGATED_LISTS - 1) ||
        ((search_size <= 1) && free_lists[list])) {
      // find blocks that are big enough and not marked with reallocation bit
      for (ptr = free_lists[list]; ptr != NULL; ptr = PRED(ptr)) {
        if ((GET_SIZE(HEADER(ptr)) >= asize) && !GET_TAG(HEADER(ptr))) {
          break;
        }
      }
      if (ptr) {
        break;
      }
    }

    search_size = search_size >> 1;
  }

  if (!ptr) {
    /* no free blocks with sufficient size were found */
    size_t heap_extend_size = MAX(asize, PAGE_SIZE);

    if (!(ptr = extend_heap(heap_extend_size))) {
      return NULL;
    }
  }

  place(ptr, asize);

  return ptr;
}

/**
 * @brief Free a block pointed by @p ptr.
 * Freeing a block is done by marking allocation bit to zero, and inserting the
 * block into segregated free block list. Additional coalescing is done.
 *
 * @param ptr
 */
void mm_free(void *ptr) {
  size_t size = GET_SIZE(HEADER(ptr));

  // unset next block's reallocation bit
  UNSET_TAG(HEADER(NEXT(ptr)));

  // unset allocation bit
  PUT(HEADER(ptr), PACK(size, 0));
  PUT(FOOTER(ptr), PACK(size, 0));

  // insert free'd block to segregated free block list
  insert_item(ptr, size);
  coalesce(ptr);
}

/**
 * @brief Reallocate a block that had been allocated already.
 * Extends the heap when necessary. New block will have additional padding space
 * to make sure next reallocation does not have to extend the heap again.
 *
 * If buffer is too small for next reallocation, next block will be marked with
 * reallocation tag. These marked free blocks won't be used by malloc or
 * coalescing.
 * Tag will clear when:
 * 1. block gets realloc'ed.
 * 2. heap gets extended.
 * 3. freeing realloc'ed block.
 *
 * @param ptr Currently allocated block pointer
 * @param size New size for the block
 * @return void* Reallocated block pointer
 */
void *mm_realloc(void *ptr, size_t size) {
  int padding_size;
  int buffered_size;
  void *new_ptr = ptr;

  if (size == 0) {
    return NULL;
  }

  // adjust block size
  size_t new_size = size;
  if (new_size > DWORD_SIZE) {
    new_size = (new_size + DWORD_SIZE + (DWORD_SIZE - 1)) & ~0x7;
  } else {
    // if no more than one dword was requested
    new_size = DWORD_SIZE * 2;
  }

  // add additional padding to block size
  new_size += REALLOCATION_BUFFER;

  buffered_size = GET_SIZE(HEADER(ptr)) - new_size;

  if (buffered_size < 0) {
    // allocate more space
    if (!GET_ALLOCATED(HEADER(NEXT(ptr))) || !GET_SIZE(HEADER(NEXT(ptr)))) {
      // next block is a free or epilogue block
      padding_size =
          GET_SIZE(HEADER(ptr)) + GET_SIZE(HEADER(NEXT(ptr))) - new_size;
      if (padding_size < 0) {
        // next block is not enough. extend heap
        int heap_extend_size = MAX(-padding_size, PAGE_SIZE);
        if (extend_heap(heap_extend_size) == NULL)
          return NULL;
        padding_size += heap_extend_size;
      }

      delete_item(NEXT(ptr));

      // block header & footer
      PUT_CLEAN(HEADER(ptr), PACK(new_size + padding_size, 1));
      PUT_CLEAN(FOOTER(ptr), PACK(new_size + padding_size, 1));
    } else {
      new_ptr = mm_malloc(new_size - DWORD_SIZE);
      memmove(new_ptr, ptr, MIN(size, new_size));
      mm_free(ptr);
    }
    buffered_size = GET_SIZE(HEADER(new_ptr)) - new_size;
  }

  if (buffered_size < REALLOCATION_BUFFER * 2) {
    // tag next block when buffer is not sufficient for another realloc
    SET_TAG(HEADER(NEXT(new_ptr)));
  }
  return new_ptr;
}

/**
 * @brief Extend the heap using system call.
 * New free block is inserted into the appropriate segregated list.
 *
 * @param bytes
 * @return void*
 */
static void *extend_heap(size_t bytes) {
  void *heap;

  // if size is not dword-aligned, make it even
  size_t words = bytes / WORD_SIZE;
  size_t size = (words % 2) ? (words + 1) * WORD_SIZE : words * WORD_SIZE;

  // extend and get new heap
  if ((ssize_t)(heap = mem_sbrk(size)) == -1) {
    return NULL;
  }

  // Modify free list header and footers
  PUT_CLEAN(HEADER(heap), PACK(size, 0));
  PUT_CLEAN(FOOTER(heap), PACK(size, 0));

  // Mark end of free list
  PUT_CLEAN(HEADER(NEXT(heap)), PACK(0, 1));

  insert_item(heap, size);

  return coalesce(heap);
}

/**
 * @brief Insert block pointer into a segregated free list.
 * Lists are segregated by size with the n-th list holding blocks with size
 * [2^n, 2^(n+1)). Each list is sorted in ascending order.
 *
 * @param item
 * @param size
 */
static void insert_item(void *item, size_t size) {
  int idx;
  void *search, *prev;

  // choose appropriate segregated list
  for (idx = 0; (size > 1) && (idx < SEGREGATED_LISTS - 1); idx++) {
    size = size >> 1;
  }

  // find place to insert pointer inside sorted list
  for (search = free_lists[idx], prev = NULL;
       search && (size > GET_SIZE(HEADER(search))); search = PRED(search)) {
    prev = search;
  }

  if (search) {
    // there is next item
    SET_PTR(PRED_PTR(item), search);
    SET_PTR(SUCC_PTR(search), item);

    if (prev) {
      // insert between
      SET_PTR(PRED_PTR(prev), item);
      SET_PTR(SUCC_PTR(item), prev);
    } else {
      // insert as first
      SET_PTR(SUCC_PTR(item), NULL);
      free_lists[idx] = item; // add block to list
    }
  } else {
    // there are no next items
    SET_PTR(PRED_PTR(item), NULL);

    if (prev) {
      // insert as last
      SET_PTR(PRED_PTR(prev), item);
      SET_PTR(SUCC_PTR(item), prev);
    } else {
      // insert as first
      SET_PTR(SUCC_PTR(item), NULL);
      free_lists[idx] = item; // add block to list
    }
  }
}

/**
 * @brief Remove block pointer from the segregated free list.
 * Lists are segregated by size with the n-th list holding blocks with size
 * [2^n, 2^(n+1)), where each list is sorted in ascending order.
 *
 * @param ptr
 */
static void delete_item(void *ptr) {
  int idx;
  size_t size = GET_SIZE(HEADER(ptr));

  // choose appropriate segregated list
  for (idx = 0; (size > 1) && (idx < SEGREGATED_LISTS - 1); idx++) {
    size = size >> 1;
  }

  void *predecessor = PRED(ptr);
  void *successor = SUCC(ptr);

  if (predecessor) {
    if (successor) {
      SET_PTR(SUCC_PTR(predecessor), successor);
      SET_PTR(PRED_PTR(successor), predecessor);
    } else {
      SET_PTR(SUCC_PTR(predecessor), NULL);
      free_lists[idx] = predecessor;
    }
  } else {
    if (successor) {
      SET_PTR(PRED_PTR(successor), NULL);
    } else {
      free_lists[idx] = NULL;
    }
  }
}

/**
 * @brief Prepend header & append footers for block @p ptr.
 * If remaining space >= MIN_SIZE, then split unavailable space into another
 * usable free block.
 *
 * @param ptr
 * @param asize Correctly adjected block size
 */
static void *place(void *ptr, size_t asize) {
  size_t payload_size = GET_SIZE(HEADER(ptr));
  size_t padding_size = payload_size - asize;

  /* Remove block from list */
  delete_item(ptr);

  if (padding_size >= MIN_SIZE) {
    // splits block
    PUT(HEADER(ptr), PACK(asize, 1));
    PUT(FOOTER(ptr), PACK(asize, 1));

    // set header & footer for unavailable block
    PUT_CLEAN(HEADER(NEXT(ptr)), PACK(padding_size, 0));
    PUT_CLEAN(FOOTER(NEXT(ptr)), PACK(padding_size, 0));

    insert_item(NEXT(ptr), padding_size);
  } else {
    // does not split block
    PUT(HEADER(ptr), PACK(payload_size, 1));
    PUT(FOOTER(ptr), PACK(payload_size, 1));
  }
  return ptr;
}

/**
 * @brief Coalesce free blocks adjacent to @p ptr. Sorts new free block into
 * the appropriate segregated free list.
 *
 * @param ptr
 * @return void*
 */
static void *coalesce(void *ptr) {
  void *prev = PREV(ptr);
  void *next = NEXT(ptr);
  size_t size = GET_SIZE(HEADER(ptr));
  size_t prev_allocated = GET_ALLOCATED(HEADER(prev));
  size_t next_allocated = GET_ALLOCATED(HEADER(next));

  if (prev_allocated && next_allocated) {
    // if both blocks are allocated
    return ptr;
  }

  if (GET_TAG(HEADER(PREV(ptr)))) {
    // if previous block was realloc-tagged, do not coalesce
    prev_allocated = 1;
  }

  delete_item(ptr);

  if (!prev_allocated) {
    // coalesce prev block
    delete_item(prev);

    size += GET_SIZE(HEADER(prev));

    PUT(HEADER(prev), PACK(size, 0));
    PUT(FOOTER(ptr), PACK(size, 0));

    ptr = prev;
  }

  if (!next_allocated) {
    // coalesce next block
    delete_item(next);

    size += GET_SIZE(HEADER(next));

    PUT(HEADER(ptr), PACK(size, 0));
    PUT(FOOTER(ptr), PACK(size, 0));
  }

  insert_item(ptr, size);

  return ptr;
}
