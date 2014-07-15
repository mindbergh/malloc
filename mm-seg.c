/*
 * mm.c
 * hbovik - Harry Bovik
 * Author:    Ming Fang
 * Mail  :    mingf@andrew.cmu.edu
 * Update:    07/13/2014
 *
 * This version is implemented using segregated list
 * LIFO order to maintain each free list.
 * 
 */

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <unistd.h>
#include "contracts.h"

#include "mm.h"
#include "memlib.h"


// Create aliases for driver tests
// DO NOT CHANGE THE FOLLOWING!
#ifdef DRIVER
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif

/*
 *  Logging Functions
 *  -----------------
 *  - dbg_printf acts like printf, but will not be run in a release build.
 *  - checkheap acts like mm_checkheap, but prints the line it failed on and
 *    exits if it fails.
 */

#ifndef NDEBUG
#define dbg_printf(...) printf(__VA_ARGS__)
#define checkheap(verbose) do {if (mm_checkheap(verbose)) {  \
                             printf("Checkheap failed on line %d\n", __LINE__);\
                             exit(-1);  \
                        }}while(0)
#else
#define dbg_printf(...)
#define checkheap(...)
#endif

/* Basic constants */
#define WSIZE         4      /* Word and header/footer size (bytes) */
#define DSIZE         8      /* Double word size (bytes) */
#define CHUNKSIZE    (1<<10) /* Extend heap by this (1K words, 4K bytes) */
#define FREE          0      /* Mark block as free */
#define ALLOCATED     1      /* Mark block as allocated */
#define SEG_LIST_SIZE 14     /* The seg list has 14 entries */

/* Private global variable */
static uint32_t *heap_listp;
static uint32_t *seg_list[SEG_LIST_SIZE];

/*
 *  Helper functions
 *  ----------------
 */

// Align p to a multiple of w bytes
static inline void* align(const void const* p, unsigned char w) {
    return (void*)(((uintptr_t)(p) + (w-1)) & ~(w-1));
}

// Check if the given pointer is 8-byte aligned
static inline int aligned(const void const* p) {
    return align(p, 8) == p;
}

// Return whether the pointer is in the heap.
static int in_heap(const void* p) {
    return p <= mem_heap_hi() && p >= mem_heap_lo();
}


/*
 *  Block Functions
 *  ---------------
 *  TODO: Add your comment describing block functions here.
 *  The functions below act similar to the macros in the book, but calculate
 *  size in multiples of 4 bytes.
 */

// Return the size of the given block in multiples of the word size
// This size doesn't count header and footer
static inline unsigned int block_size(const uint32_t* block) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));

    return (block[0] & 0x3FFFFFFF);
}

// Return true if the block is free, false otherwise
static inline int block_free(const uint32_t* block) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));

    return !(block[0] & 0x40000000);
}

// Mark the given block as free(1)/alloced(0) by marking the header and footer.
static inline void block_mark(uint32_t* block, int free) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));
    free = !free;
    unsigned int next = block_size(block) + 1;
    block[0] = free ? block[0] & (int) 0xBFFFFFFF : block[0] | 0x40000000;
    block[next] = block[0];
}

// Return a pointer to the memory malloc should return
static inline uint32_t* block_mem(uint32_t* const block) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));
    REQUIRES(aligned(block + 1));

    return block + 1;
}

// Return the header to the predecessor free block
static inline uint32_t* block_pred(uint32_t* const block) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));

    unsigned int address = (unsigned int)heap_listp + block[1];

    ENSURES((uint32_t *)address != NULL);
    ENSURES(in_heap((uint32_t *)address));
    if ((uint32_t *)address == heap_listp)
        return NULL;
    else 
        return (uint32_t *)address;
}

// Return the header to the successor free block
static inline uint32_t* block_succ(uint32_t* const block) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));

    unsigned int address = (unsigned int)heap_listp + block[2];

    ENSURES((uint32_t *)address != NULL);
    ENSURES(in_heap((uint32_t *)address));

    if ((uint32_t *)address == heap_listp)
        return NULL;
    else 
        return (uint32_t *)address;
}

// Return the header to the previous block
static inline uint32_t* block_prev(uint32_t* const block) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));

    return block - block_size(block - 1) - 2;
}

// Return the header to the next block
static inline uint32_t* block_next(uint32_t* const block) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));

    return block + block_size(block) + 2;
}

// Set given value to the given block 
static inline void set_val(uint32_t* const block, unsigned int val) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));

    (*(unsigned int *)(block) = val);
}

// Set the size of the given block in multiples of 4 bytes
static inline void set_val(uint32_t* const block, unsigned int size) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));

    set_val(block, size);
}

/*
 * Set the pred and succ of the given free block
 * Since the whole memory space is 2^32 bytes
 * I can compress the 8 bytes address into 4 bytes
 * by computing its offest to heap_listp
 */
static inline void set_ptr(uint32_t* const block, 
                          uint32_t* const pred_block, 
                          uint32_t* const succ_block) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));

    unsigned int pred_offest 
    unsigned int succ_offest

    if (pred_block == NULL)
        pred_offest = 0;
    else 
        pred_offest = (unsigned int)pred_block 
                               - (unsigned int)heap_listp;

    if (succ_block == NULL)
        succ_offest = 0;
    else
        succ_offest = (unsigned int)succ_block 
                               - (unsigned int)heap_listp;   

    set_val(block + 1 , pred_offest);
    set_val(block + 2 , succ_offest);    
}


// Return the index to the segregated list according to given words size
static inline int find_index(unsigned int words) {
    REQUIRES(words % 2 == 0);

    if (words == 2) 
        return 0;
    else if (words == 4)
        return 1;
    else if(words >= 6 && words <= 8)
        return 2; 
    else if(words >= 10 && words <= 16)
        return 3;     
    else if(words >= 18 && words <= 32)
        return 4;
    else if(words >= 34 && words <= 64)
        return 5;
    else if(words >= 66 && words <= 128)
        return 6;
    else if(words >= 130 && words <= 256)
        return 7;
    else if(words >= 258 && words <= 512)
        return 8;
    else if(words >= 514 && words <= 1024)
        return 9;
    else if(words >= 1026 && words <= 2048)
        return 10;
    else if(words >= 2050 && words <= 4096)
        return 11;
    else if(words >= 4098 && words <= 8192)
        return 12;
    else
        return 13;
}

// Insert the given free block into seg list according to its size
static inline void block_insert(uint32_t* block) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));

    int index = find_index(block_size(block));
    uint32_t *old_block = seg_list[index];

    if (old_block == NULL) { // this list is empty
        set_ptr(block, NULL, NULL);
        seg_list[index] = block;
    } else {                 // this list is not empty
        ENSURES(block_pred(old_block) == NULL);
        ENSURES(in_heap(block_succ(old_block)));

        set_ptr(old_block, block, block_succ(old_block));
        set_ptr(block, NULL, old_block);
    }
}

// Delete the given block from the seg list
static inline void block_delete(uint32_t* block) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));


    uint32_t *pred = block_pred(block);
    uint32_t *succ = block_succ(block);
    int index = find_index(block_size(block));

    if (pred == NULL && succ == NULL) 
        seg_list[index] = NULL;
    else if (pred == NULL && succ != NULL) {
        set_ptr(succ, NULL, block_succ(succ));
        seg_list[index] = succ;
    } else if (pred != NULL && succ == NULL) {
        set_ptr(pred, block_pred(pred), NULL);
    } else {
        set_ptr(pred, block_pred(pred), succ);
        set_ptr(succ, pred, block_succ(succ));
    }
}


/*
 * Merge block with adjacent free blocks
 * Return: the pointer to the new free block 
 */
static void *coalesce(void *block) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));

    int prev_free = block_free(block_prev(block));
    int next_free = block_free(block_next(block));
    unsigned int words = block_size(block);
    int index;

    if (prev_free && next_free) {       // Case 4, both free
        uint32_t *prev_block = block_prev(block);
        uint32_t *next_block = block_next(block);
        block_delete(prev_block);
        block_delete(next_block);

        words += block_size(prev_block) + block_size(next_block) + 4;
        set_size(prev_block, words);
        block_mark(prev_block, FREE);
        block = (void *)prev_block;

        block_insert(block);
    }

    else if (!prev_free && next_free) { // Case 2, next if free
        uint32_t *next_block = block_next(block);
        block_delete(next_block);

        words += block_size(next_block) + 2;
        set_size(block, words);
        block_mark(block, FREE);  

        block_insert(block);      
    }

    else if (prev_free && !next_free) { // Case 3, prev is free
        uint32_t *prev_block = block_prev(block);
        block_delete(prev_block);

        words += block_size(prev_block) + 2;
        set_size(prev_block, words);
        block_mark(prev_block, FREE);
        block = (void *)prev_block;

        block_insert(block);
    }

    else {                              // Case 1, both unfree
        block_insert(block);
        return block;
    }
    return block;
 } 

/*
 * Extends the heap with a new free block
 * Return: the pointer to the new free block 
 *         NULL on error.
 */
static void *extend_heap(unsigned int words) {
    REQUIRES(words > 4);

    uint32_t *block;
    int index;
    
    /* Ask for 2 more words for header and footer */
    words = (words % 2) ? (words + 3) : words + 2;
    if ((long)(block = mem_sbrk(words * WSIZE)) == -1)
        return NULL;

    block--;          // back step 1 since the last one is the epi block
    set_size(block, words);
    block_mark(block, FREE);

    // New eqilogue block    
    set_size(block_next(block), 0);
    (block_next(block))[0] |= 0x40000000;
    //block_mark(block_next(block), ALLOCATED);

    return coalesce(block);    // Coalesce if necessary
 }

/*
 * Find the fit using first fit search
 * Return: the pointer to the found free block 
 *         NULL on no matching.
 */
static void *find_fit(unsigned int awords) {
    REQUIRES(awords >= 2);
    REQUIRES(awords % 2 == 0);

    uint32_t *block;
    int index = find_index(awords);

    for (int i = index; i < SEG_LIST_SIZE; ++i) {        
        if (seg_list[i] == NULL)
            continue;
        for (block = seg_list[i]; block != NULL; block = block_succ(block)) {
            if (block_size(block) >= awords)
                return block;
        }
    }
    return NULL;
 }

/*
 * Place the block and potentially split the block
 * Return: Nothing
 */
static void place(void *block, unsigned int awords) {
    REQUIRES(awords >= 2 && awords % 2 == 0);
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));

    unsigned int cwords = block_size(block);
    block_delete(block);      // delete block from the seg list

    if ((cwords - awords) >= 4) {
        set_size(block, awords);
        block_mark(block, ALLOCATED);
        block = block_next(block);
        set_size(block, cwords - awords - 2);
        block_mark(block, FREE);
        block_insert(block);
    } else {
        set_size(block, cwords);
        block_mark(block, ALLOCATED);
    }    
 }

/*
 *  Malloc Implementation
 *  ---------------------
 *  The following functions deal with the user-facing malloc implementation.
 */

/*
 * Initialize: return -1 on error, 0 on success.
 */
int mm_init(void) {

    /* Initialize the seg_list with NULL */
    for (int i = 0; i < SEG_LIST_SIZE; ++i) {
        seg_list[i] = NULL;
    }

    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)
        return -1;
    set_size(heap_listp, 0);                 // Allignment padding
    set_size(heap_listp + 1, 0);             // Pro of 0 size
    set_size(heap_listp + 3, 0);             // Epi of 0 size
    (heap_listp + 3)[0] |= 0x40000000;
    block_mark(heap_listp + 1, ALLOCATED);   // Mark prologue as allocated

    heap_listp += 3;                            
    
    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE - 2) == NULL)
        return -1;
    return 0;
}



/*
 * malloc
 */
void *malloc (size_t size) {
    checkheap(1);  // Let's make sure the heap is ok!
    unsigned int awords;  //Adjusted block size
    unsigned int ewords;  //Amount to extend heap if no matching
    uint32_t *block;

    /* Ignore 0 requests */
    if (size == 0)
        return NULL;
    /* Adjust size to include alignment and convert to multipes of 4 bytes */
    if (size <= DSIZE)
        awords = 2;
    else
        awords = (((size) + (DSIZE-1)) & ~0x7) / WSIZE;

    /* Search the free list for a fit */
    if ((block = find_fit(awords)) != NULL) {
        place(block, awords);
        return block_mem(block);
    }

    /* No fit found. Get more memory and place the block */ 
    ewords = awords > CHUNKSIZE ? awords : CHUNKSIZE - 2;
    if ((block = extend_heap(ewords)) == NULL)
            return NULL;
    place(block, awords);
    return block_mem(block);
}

/*
 * free
 */
void free (void *ptr) {
    /* If ptr is NULL, no operation is performed. */    
    if (ptr == NULL)
        return;

    uint32_t* block = (uint32_t*)(ptr) - 1;

    block_mark(block, FREE);
    coalesce(block);
}

/*
 * realloc - you may want to look at mm-naive.c
 */
void *realloc(void *oldptr, size_t size) {
    oldptr = oldptr;
    size = size;
    return NULL;
}

/*
 * calloc - you may want to look at mm-naive.c
 */
void *calloc (size_t nmemb, size_t size) {
    nmemb = nmemb;
    size = size;
    return NULL;
}

// Returns 0 if no errors were found, otherwise returns the error
int mm_checkheap(int verbose) {
    verbose = verbose;
    uint32_t *block = heap_listp - 2;
    
    //Check prologue blocks.
    if (block_size(block) == 0) {
        if(block_free(block)) {
            if (verbose)
                printf("Pro block should not be free, header = %x\n", block[0]);
            return -1;
        }        
    }

    for (block = heap_listp; block_size(block) > 0; block = block_next(block)) {        

        //Check each block’s address alignment.
        if (align(block + 1, 8) != block + 1) {
            if (verbose)
                printf("Block address alignment error\n");
            return -1;
        }

        //Check heap boundaries.
        if (!in_heap(block)) {
            if (verbose)
                printf("Block isn't in heap\n");
            return -1;
        }
        
        /* Check each block’s header and footer: 
        size (minimum size, alignment), previous/next allocate/
        free bit consistency, header and footer matching each other. */

        unsigned int words = block_size(block);
        if (words < 2) {
            if (verbose)
                printf("Block size is less then 8 bytes\n");
            return -1;
        }
        if (words % 2 != 0) {
            if (verbose)
                printf("Header %x, size %d is not a multiples of 8 bytes\n",
                      block[0],
                      words);
            return -1;
        }

        unsigned int next = block_size(block) + 1;        
        if (block[next] != block[0]) {
            if (verbose)
                printf("Header and footer should be identical\n");
            return -1;
        }

        //Check coalescing: no two consecutive free blocks in the heap.
        if (block_free(block)) {
            if (block_free(block_prev(block)) || block_free(block_next(block))) {
                if (verbose)
                    printf("There should be no consecutive free blocks\n");
                return -1;
            }
        }
    }    

    if (block_free(block)) {
        if (verbose)
            printf("Epi block should not be free\n");
        return -1;
    }

    return 0;
}
