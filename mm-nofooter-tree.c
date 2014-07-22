/*
 * mm.c
 * hbovik - Harry Bovik
 * Author:    Ming Fang
 * Mail  :    mingf@andrew.cmu.edu
 * Update:    07/13/2014
 *
 * This version is implemented using segregated list
 * LIFO order to maintain each free list.
 * No footer at allocated block
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
#define CHUNKSIZE     65    /* Extend heap by this (1K words, 4K bytes) */
#define FREE          1      /* Mark prev block as free */
#define ALLOCATED     0      /* Mark prev block as allocated */
#define SEG_LIST_SIZE 19     /* The seg list has 14 entries */
#define VERBOSE       0      /* Indicator to print debug info */
#define ADDRESS       1      /* Operation on address order */
#define SIZE          0      /* Operation on size order  */

/* Private global variable */
static uint32_t *heap_listp;
static uint32_t **seg_list;
static uint32_t *root;

/* Function prototypes */ 
static inline void* align(const void const* p, unsigned char w);
static inline int aligned(const void const* p);
static int in_heap(const void* p);
static inline unsigned int block_size(const uint32_t* block);
static inline int block_free(const uint32_t* block);
static inline int block_free(const uint32_t* block);
static inline void block_mark_free(uint32_t* block, int alloc);
static inline void block_mark_allo(uint32_t* block, int alloc);
static inline uint32_t* block_mem(uint32_t* const block);
static inline uint32_t* block_block(uint32_t* const ptr);
static inline uint32_t* block_pred(uint32_t* const block);
static inline uint32_t* block_succ(uint32_t* const block);
static inline uint32_t* block_prev(uint32_t* const block);
static inline uint32_t* block_next(uint32_t* const block);
static inline void set_val(uint32_t* const block, unsigned int val);
static inline void set_size(uint32_t* const block, unsigned int size) ;
static inline void set_ptr(uint32_t* const block, 
                          uint32_t* const pred_block, 
                          uint32_t* const succ_block);
static inline int find_index(unsigned int words);
static int in_list(uint32_t* block) ;
static inline void block_insert(uint32_t* block);
static inline void block_delete(uint32_t* block);
static inline uint32_t * put(uint32_t * block, uint32_t * root);
static inline uint32_t * epi_block();

/*    Segregated List 
 * Size(DWORD)    Entry
 * 1                0
 * 2                1
 * 3-4              2
 * 5-8              3
 * 9-16             4
 * 17-32            5
 * 33-64            6
 * 65-128           7
 * 129-256          8
 * 257-512          9
 * 513-1024         10
 * 1025-2048        11
 * 2049-4096        12
 * 4097-Inf         13
 */


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

// Return true if the prev block is free, false otherwise
static inline int block_prev_free(const uint32_t* block) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));

    return !(block[0] & 0x80000000);
}

/* Mark the given block as free(1) by marking the header and footer.
 * Addionally mark if the prev block is free or not
 * Arguments: free is FREE      if the prev is free
 *                    ALLOCATED if the prev is allocated 
 */
static inline void block_mark_free(uint32_t* block, int alloc) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));
    unsigned int next = block_size(block) + 1;
    block[0] = alloc ? block[0] & (int) 0x3FFFFFFF : (block[0] | 0x80000000) & (int) 0xBFFFFFFF;
    block[next] = block[0];
}

/* Mark the given block as alloced by marking only header
 * Addionally mark if the prev block is free or not
 * Arguments: free is FREE      if the prev is free
 *                    ALLOCATED if the prev is allocated 
 */
static inline void block_mark_allo(uint32_t* block, int alloc) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));
    block[0] = alloc ? (block[0] | 0x40000000) & (int) 0x7FFFFFFF : block[0] | 0xC0000000;
}

// Return a pointer to the memory malloc should return
static inline uint32_t* block_mem(uint32_t* const block) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));
    REQUIRES(aligned(block + 1));
    if (VERBOSE)
        printf("Heap size = %d bytes \n", (int)mem_heapsize());
    return block + 1;
}

// Return a pointer to block of what malloc returns
static inline uint32_t* block_block(uint32_t* const ptr) {
    REQUIRES(ptr != NULL);
    REQUIRES(in_heap(ptr - 1));
    REQUIRES(aligned(ptr));

    return ptr - 1;
}

// Return the header to the predecessor free block
static inline uint32_t* block_pred(uint32_t* const block) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));
    REQUIRES(block_size(block) >= 2);

    uint32_t * address = heap_listp + block[1];

    ENSURES(address != NULL);
    ENSURES(in_heap(address));

    if (address == heap_listp)
        return NULL;
    else 
        return address;
}

// Return the header to the successor free block
static inline uint32_t* block_succ(uint32_t* const block) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));
    REQUIRES(block_size(block) >= 2);

    uint32_t * address = heap_listp + block[2];

    ENSURES(address != NULL);
    ENSURES(in_heap(address));

    if (address == heap_listp)
        return NULL;
    else 
        return address;
}

// Return the left child of the given free block
static inline uint32_t* left(uint32_t* const block) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));
    REQUIRES(block_size(block) >= 4);

    uint32_t * address = heap_listp + block[3];

    ENSURES(address != NULL);
    ENSURES(in_heap(address));

    if (address == heap_listp)
        return NULL;
    else 
        return address;
}

// Return the right child of the given free block
static inline uint32_t* right(uint32_t* const block) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));
    REQUIRES(block_size(block) >= 4);

    uint32_t * address = heap_listp + block[4];

    ENSURES(address != NULL);
    ENSURES(in_heap(address));

    if (address == heap_listp)
        return NULL;
    else 
        return address;
}

// Return the header to the previous block
static inline uint32_t* block_prev(uint32_t* const block) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));
    REQUIRES(block_prev_free(block));

    return block - block_size(block - 1) - 2;
}

// Return the header to the next block
static inline uint32_t* block_next(uint32_t* const block) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));
    if (block_free(block))
        return block + block_size(block) + 2;
    else
        return block + block_size(block) + 1;
}

// Set given value to the given block 
static inline void set_val(uint32_t* const block, unsigned int val) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));

    (*(unsigned int *)(block) = val);
}

// Set the size of the given block in multiples of 4 bytes
static inline void set_size(uint32_t* const block, unsigned int size) {
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

    unsigned int pred_offest; 
    unsigned int succ_offest;

    if (pred_block == NULL)
        pred_offest = 0;
    else 
        pred_offest = pred_block - heap_listp;

    if (succ_block == NULL)
        succ_offest = 0;
    else
        succ_offest = succ_block - heap_listp;

    //printf("pred_off = %d, succ_off = %d\n", pred_offest, succ_offest);
    set_val(block + 1 , pred_offest);
    set_val(block + 2 , succ_offest);
    ENSURES(block_pred(block) == pred_block);
    ENSURES(block_succ(block) == succ_block);    
}

/*
 * Set the left and right child of the given free block
 * The free block has a minimum size requirement of 4 words
 */
static inline void set_chd_ptr(uint32_t* const block, 
                          uint32_t* const left, 
                          uint32_t* const right) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));

    unsigned int left_offest; 
    unsigned int right_offest;

    if (pred_block == NULL)
        pred_offest = 0;
    else 
        pred_offest = pred_block - heap_listp;

    if (succ_block == NULL)
        succ_offest = 0;
    else
        succ_offest = succ_block - heap_listp;


    //printf("pred_off = %d, succ_off = %d\n", pred_offest, succ_offest);
    set_val(block + 3 , left_offest);
    set_val(block + 4 , right_offest);
    ENSURES(left(block) == left);
    ENSURES(right(block) == right);  
}


// Return the index to the segregated list according to given words size
static inline int find_index(unsigned int words) {

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
    else if(words >= 8194 && words <= 16384)
        return 13;
    else if(words >= 16386 && words <= 32768)
        return 14;
    else if(words >= 32770 && words <= 65536)
        return 15;
    else if(words >= 65538 && words <= 131072)
        return 16;
    else if(words >= 131072 && words <= 262144)
        return 17;
    else
        return 18;
}

// Return whether the pointer is in the seg list.
static int in_list(uint32_t* block) {
    uint32_t *pred = block_pred(block);
    uint32_t *succ = block_succ(block);
    int index = find_index(block_size(block));

    if (pred == NULL && succ == NULL) { 
        // The list has only one block
        return seg_list[index] == block;
    } else if (pred == NULL && succ != NULL) {
        // This block is at the head, seg_list[index] == block
        return seg_list[index] == block && block_pred(succ) == block;
    } else if (pred != NULL && succ == NULL) {
        // This block is at the tail
        return block_succ(pred) == block;
    } else {
        // This block is the middle of somewhere
        return block_succ(pred) == block && block_pred(succ) == block;
    }
}

// Insert the given free block into seg list according to its size
static inline void block_insert(uint32_t* block) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));

    int index = find_index(block_size(block));
    //printf("index = %d, size = %d\n", index, block_size(block));
    uint32_t *old_block = seg_list[index];

    if (old_block == NULL) { // this list is empty
        set_ptr(block, NULL, NULL);
        seg_list[index] = block;
    } else {                 // this list is not empty
        ENSURES(block_pred(old_block) == NULL);
        ENSURES(block_succ(old_block) == NULL || in_heap(block_succ(old_block)));

        set_ptr(old_block, block, block_succ(old_block));
        set_ptr(block, NULL, old_block);
        seg_list[index] = block;
    }
    ENSURES(in_list(block));
}

// Delete the given block from the seg list
static inline void block_delete(uint32_t* block) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));


    uint32_t *pred = block_pred(block);
    uint32_t *succ = block_succ(block);
    int index = find_index(block_size(block));

    if (pred == NULL && succ == NULL) { 
        // The list has only one block
        seg_list[index] = NULL;
    } else if (pred == NULL && succ != NULL) {
        // This block is at the head, seg_list[index] == block
        set_ptr(succ, NULL, block_succ(succ));
        seg_list[index] = succ;
    } else if (pred != NULL && succ == NULL) {
        // This block is at the tail
        set_ptr(pred, block_pred(pred), NULL);
    } else {
        // This block is the middle of somewhere
        set_ptr(pred, block_pred(pred), succ);
        set_ptr(succ, pred, block_succ(succ));
    }
}

static inline uint32_t * put(uint32_t * block, uint32_t * root) {
    if (root == NULL) {
        set_ptr(block, NULL, NULL)
        set_chd_ptr(block, NULL, NULL);
        return block;
    }

    int cmp = cmp_size(block, root);

    if (cmp > 0) 
        set_chd_ptr(root, left(root), put(block, right(root)));
    else if (cmp < 0) 
        set_chd_ptr(root, put(block, left(root)), right(root));
    else {
        /* At this point, root is the ptr of the first blk of the same size 
         * we add blk into this address ordered tree */
        root = add(block, root);
    }
    return root;
}

static inline uint32_t * del(uint32_t * block, uint32_t * root) {
    if (root == NULL) return NULL;

    int cmp = cmp_size(block, root);

    if (cmp < 0)
        set_ptr(root, del(block, block_pred(root)), block_succ(root));
    else if (cmp > 0)
        set_ptr(root, block_pred(root), del(block, block_succ(root)));
    else {
        /* At this point, root is the ptr of the first blk of the same size 
         * we del blk from this address ordered tree */
        root = take(block, root);
    }

}

/* Add given block to given tree, the given tree contains blocks of the 
 * same size, arranges by the address order of blocks
 */
static inline uint32_t * add(uint32_t * block, uint32_t * root) {
    if (root == NULL) {
        set_ptr(block, NULL, NULL);
        return block;
    }

    int cmp = cmp_add(block, root);
    ENSURES(cmp != 0);

    if (cmp > 0) 
        set_ptr(root, block_pred(root), add(block, block_succ(root)));
    else 
        set_ptr(root, add(block, block_pred(root)), block_succ(root));
    return root;
}

/* Delete given block from given tree, the given tree contains blocks of the 
 * same size, arranges by the address order of blocks
 */
static inline uint32_t * take(uint32_t * block, uint32_t * root) {
    if (root == NULL) return NULL;

    int cmp = cmp_add(block, root);
    ENSURES(cmp != 0);

    if (cmp > 0) 
        set_ptr(root, block_pred(root), take(block, block_succ(root)));
    else if (cmp < 0)
        set_ptr(root, take(block, block_pred(root)), block_succ(root));
    else {
        ENSURES(block == root);
        if (block_succ(root) == NULL) return block_pred(root);
        if (block_pred(root) == NULL) return block_succ(root);
        uint32_t * t = root;
        root = minimum(block_succ(root), ADDRESS);
        set_ptr(root, block_pred(t), deleteMin(block_succ(t), ADDRESS));
    }
    return root;
}

/* Retrun the minimun block of from given tree, according to given order
 */
static inline uint32_t * minimum(uint32_t * block, int order) {
    switch (order) {
        case ADDRESS:
            if (block_pred(block) == NULL)
                return block;
            else
                return minimum(block, ADDRESS);
        case SIZE:
            if (left(block) == NULL)
                return block;
            else
                return minimum(block, SIZE);
    }
}

/* Delete the minimun block of from given tree, according to given order
 */
static inline uint32_t * deleteMin(uint32_t * block, int order) {
    switch (order) {
        case ADDRESS:
            if (block_pred(block) == NULL)
                return block_succ(block);
            else {
                set_ptr(block, deleteMin(block, ADDRESS), block_succ(block));
                return block;
            }
        case SIZE:
            if (left(block) == NULL)
                return right(block);
            else {
                set_chd_ptr(block, deleteMin(block, SIZE), right(block));
                return block;
            }
    }
}

/* Compare the size of two given blocks
 * Return:  1, if the 1st one is greater
 *         -1, if the 2nd one is greater
 *          0, if two are equal
 */
static inline int cmp_size(uint32_t * this, uint32_t * that) {
    unsigned int this_size = block_size(this);
    unsigned int that_size = block_size(that);

    if (this_size > that_size)
        return 1;
    else if (this_size < that_size) 
        return -1;
    else
        return 0;
}

/* Compare the add of two given blocks
 * Return:  1, if the 1st one is greater
 *         -1, if the 2nd one is greater
 *          0, if two are equal
 */
static inline int cmp_add(uint32_t * this, uint32_t * that) {

    if (this > that)
        return 1;
    else if (this < that) 
        return -1;
    else
        return 0;
}


// Return the pointer to the last block in the heap.
static inline uint32_t * epi_block() {
    return (uint32_t *)((char *)mem_heap_hi() - 3);
}


/*
 * Merge block with adjacent free blocks
 * Return: the pointer to the new free block 
 */
static void *coalesce(void *block) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));

    uint32_t *prev_block = NULL;
    uint32_t *next_block = block_next(block);
    int prev_free = block_prev_free(block);
    int next_free = block_free(next_block);
    unsigned int words = block_size(block);

    if (prev_free)
        prev_block = block_prev(block);
    if (!block_free(block))
        words -= 1;
    

    if (prev_free && next_free) {       // Case 4, both free

        block_delete(prev_block);
        block_delete(next_block);

        words += block_size(prev_block) + block_size(next_block) + 4;
        set_size(prev_block, words);
        block_mark_free(prev_block, ALLOCATED);
        block = (void *)prev_block;

        block_insert(block);
        ENSURES(in_list(block));    
    }

    else if (!prev_free && next_free) { // Case 2, next if free

        block_delete(next_block);

        words += block_size(next_block) + 2;
        set_size(block, words);
        block_mark_free(block, ALLOCATED);  

        block_insert(block);
        ENSURES(in_list(block));      
    }

    else if (prev_free && !next_free) { // Case 3, prev is free
        block_delete(prev_block);

        words += block_size(prev_block) + 2;
        set_size(prev_block, words);
        block_mark_free(prev_block, ALLOCATED);
        block = (void *)prev_block;

        block_insert(block);
        ENSURES(in_list(block));
    }

    else {                              // Case 1, both unfree
        set_size(block, words);
        block_mark_free(block, ALLOCATED);
        block_insert(block);
        ENSURES(in_list(block));
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
    //REQUIRES(words >= 3);
    REQUIRES(words % 2 == 1);
    uint32_t *block;
    uint32_t *next;
    
    words += 1;   //Ask 1 more for the header
    if (VERBOSE)
        printf("Extend Words = %d bytes\n", words * 4);
    if ((long)(block = mem_sbrk(words * WSIZE)) == -1)
        return NULL;

    block--;          // back step 1 since the last one is the epi block
    
    if (block_prev_free(block)) {
        set_size(block, words - 2);
        block_mark_free(block, FREE);
        ENSURES(block_prev_free(block));
    }
    else {
        set_size(block, words - 2);
        block_mark_free(block, ALLOCATED);
        ENSURES(!block_prev_free(block));
    }
    ENSURES(block != NULL);
    // New eqilogue block
    next = block_next(block);
    set_size(next, 0);
    //*next |= 0x40000000;
    block_mark_allo(next, FREE);

    ENSURES(!block_free(next));
    ENSURES(block_size(next) == 0);
    block = coalesce(block);    // Coalesce if necessary
    ENSURES(in_list(block));
    return block;
 }

/*
 * Find the fit using first fit search
 * Return: the pointer to the found free block 
 *         NULL on no matching.
 */
static void *find_fit(unsigned int awords) {
    REQUIRES(awords >= 2);
    REQUIRES(awords % 2 == 0);

    uint32_t *block = NULL;
    uint32_t *res = block;
    int found = 0;
    unsigned int words = 1 << 31;
    unsigned int thiswords = 0;
    int index = find_index(awords);

    for (int i = index; i < SEG_LIST_SIZE; ++i) {
        //printf("index in finding = %d\n", i);        
        if (seg_list[i] == NULL)
            continue;
        for (block = seg_list[i]; block != NULL; block = block_succ(block)) {
            thiswords = block_size(block);
            if (thiswords >= awords) {
                if (thiswords < words) {
                    res = block;
                    words = thiswords;
                }
                found = 1;
                //return block;
            }
        }
        if (found) 
            break;
    }
    return res;
 }

/*
 * Place the block and potentially split the block
 * Return: Nothing
 */
static void place(void *block, unsigned int awords) {

    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));
    REQUIRES(in_list(block));

    unsigned int cwords = block_size(block); //the size of the given freeblock
    block_delete(block);      // delete block from the seg list
    
    ENSURES(!in_list(block));

    if (cwords >= (awords + 3)) {
        ENSURES(!block_prev_free(block));
        set_size(block, awords);        
        block_mark_allo(block, ALLOCATED);

        block = block_next(block);
        set_size(block, cwords - awords - 1);

        block_mark_free(block, ALLOCATED);

        block_insert(block);

        ENSURES(in_list(block));
    } else {
        ENSURES(block_prev_free(block) == 0);
        set_size(block, cwords + 1);
        block_mark_allo(block, ALLOCATED);

        block = block_next(block);
        ENSURES(!block_free(block));
        block_mark_allo(block, ALLOCATED);
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
    seg_list = mem_sbrk(SEG_LIST_SIZE * sizeof(uint32_t *));
    for (int i = 0; i < SEG_LIST_SIZE; ++i) {
        seg_list[i] = NULL;
    }

    if ((heap_listp = mem_sbrk(2 * WSIZE)) == (void *)-1)
        return -1;
    set_size(heap_listp, 0);             // Pro of 0 size
    set_size(heap_listp + 1, 0);             // Epi of 0 size
    block_mark_allo(heap_listp, ALLOCATED);   // Mark prologue as allocated
    block_mark_allo(heap_listp + 1, ALLOCATED);   // Mark epilogue as allocated
    ENSURES(!block_prev_free(heap_listp));
    ENSURES(!block_prev_free(heap_listp + 1));
    
    /* Extend the empty heap with a free block of CHUNKSIZE bytes
     * extend_heap would ask for 2 more words */
    if (extend_heap(CHUNKSIZE) == NULL)
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
    uint32_t * epi = epi_block();

    if (VERBOSE)
        printf("Malloc %d bytes\n", (int)size);

    /* Ignore 0 requests */
    if (size == 0)
        return NULL;
    /* Adjust size to include alignment and convert to multipes of 4 bytes
     * Recall that alloc block only has header, therefore the min size should be  
     * 12, and then 20, 28.... */
    if (size <= 12)
        awords = 3;
    else
        awords = 3 + (((size - 12) + (DSIZE-1)) & ~0x7) / WSIZE;

    if (VERBOSE)
        printf("Awords =  %d\n", awords);

    /* Search the free list for a fit */
    if ((block = find_fit(awords - 1)) != NULL) {
        place(block, awords);
        //printf("3\n");
        return block_mem(block);        
    }

    /* No fit found. Get more memory and place the block */ 
    if (awords > CHUNKSIZE)
        ewords = awords;
    else if (0)
        ewords = awords;
    else
        ewords = awords;

    if (block_prev_free(epi)) {
        unsigned int last_size = block_size(block_prev(epi));
        if (VERBOSE)
            printf("last size =  %d\n", last_size);
        ENSURES(last_size + 1 < ewords);
        ewords = ewords - last_size - 2;
        //ewords += 2;
        //printf("1\n");
    }

    if (VERBOSE)
        printf("Ewords =  %d\n", ewords);

    if ((block = extend_heap(ewords)) == NULL)
        return NULL;
    place(block, awords);
    return block_mem(block);
}

/*
 * free
 */
void free (void *ptr) {
    checkheap(1);  // Let's make sure the heap is ok!
    /* If ptr is NULL, no operation is performed. */    
    if (ptr == NULL)
        return;

    if (VERBOSE == 1)
        printf("Free %p \n", ptr);

    uint32_t* block = block_block(ptr);
    (block_next(block))[0] &= (int) 0x7FFFFFFF;
    coalesce(block);
}

/*
 * realloc - you may want to look at mm-naive.c
 */
void *realloc(void *oldptr, size_t size) {
    checkheap(1);  // Let's make sure the heap is ok!
    if (oldptr == NULL)   // if oldptr is NULL, this works as malloc(size)
        return malloc(size);
    if (size == 0) {      // if size is 0, this works as free(oldptr)
        free(oldptr);
        return NULL;
    }

    if (VERBOSE)
        printf("Realloc %d bytes\n", (int)size);

    uint32_t *block = block_block(oldptr);

    REQUIRES(in_heap(block));
    REQUIRES(!block_free(block));



    unsigned int words = block_size(block);  // old size in words
    unsigned int nwords;                      // new size in words
    uint32_t * ptr;                           // temp ptr

    /* Adjust size to include alignment and convert to multipes of 4 bytes */
    if (size <= 12)
        nwords = 3;
    else
        nwords = 3 + (((size - 12) + (DSIZE-1)) & ~0x7) / WSIZE;

    /* if new size is the same as old size or the old size is larger but no larger
     * than 4 words, return oldptr without spliting */
    //printf("RE, words = %d, nwords = %d\n", words, nwords);
    if (nwords == words || (words > nwords && words - nwords < 4))
        return oldptr;
    else if ((words > nwords && words - nwords >= 4)) {
        /* if old size is at least 4 words larger than new size
         * return oldptr with spliting */      
        
        if (block_prev_free(block)) {
            set_size(block, nwords);
            block_mark_allo(block, FREE);        
        } else {
            set_size(block, nwords);
            block_mark_allo(block, ALLOCATED);
        }

        ptr = block_next(block);
        ENSURES(words - nwords - 2 < words);
        set_size(ptr, words - nwords - 2);
        block_mark_free(ptr, ALLOCATED);

        // if the next block is free, do coalescence
        uint32_t *next = block_next(ptr);
        if (block_free(next)) {
            block_delete(next);
            set_size(ptr, block_size(ptr) + block_size(next) + 2);
            block_mark_free(ptr, ALLOCATED);
            block_insert(ptr);
        } else {
            block_mark_allo(next, FREE);
            block_insert(ptr);
        }
        return oldptr;
    } else {
        /* if old size is smaller than new size, look for more space */
        ptr = block_next(block);
        if (block_free(ptr)) {
            ENSURES(in_list(ptr));

            // if next block is free
            unsigned int owords = block_size(ptr);  //size of next block
            int remain = owords + 1 - (nwords - words);
            if (remain >= 3) {
                // the next free block is enough large to split
                block_delete(ptr);
                

                if (block_prev_free(block)) {
                    set_size(block, nwords);
                    block_mark_allo(block, FREE);
                } else {
                    set_size(block, nwords);
                    block_mark_allo(block, ALLOCATED);
                }
                ptr = block_next(block);
                set_size(ptr, remain - 1);
                block_mark_free(ptr, ALLOCATED);
                block_insert(ptr);
                return oldptr;
            } else if (remain >= 0) {
                // the next free block can not split
                block_delete(ptr);
                

                if (block_prev_free(block)) {
                    set_size(block, words + owords + 2); 
                    block_mark_allo(block, FREE);
                } else {
                    set_size(block, words + owords + 2);
                    block_mark_allo(block, ALLOCATED);
                }

                ptr = block_next(block);
                ENSURES(!block_free(ptr));
                block_mark_allo(ptr, ALLOCATED);
                return oldptr;
            }
        } 
        /* the next free block is too small, or
         * next block is not free, malloc whole new one. */
        ptr = malloc(size);
        /* Copy the old data. */
        memcpy(ptr, oldptr, block_size(block) * WSIZE);
        /* Free the old block. */
        free(oldptr);
        return ptr;
    }
}


/*
 * calloc - you may want to look at mm-naive.c
 */
void *calloc (size_t nmemb, size_t size) {
  size_t bytes = nmemb * size;
  void *newptr;

  newptr = malloc(bytes);
  memset(newptr, 0, bytes);

  return newptr;
}

// Returns 0 if no errors were found, otherwise returns the error
int mm_checkheap(int verbose) {
    
    uint32_t *block = heap_listp;
    int count_iter = 0;
    int count_list = 0;
    
    //Check prologue blocks.
    if (block_size(block) != 0) {
        if (verbose)
            printf("Pro block should be zero size, header = %x\n", block[0]);
        return -1;         
    }

    if(block_free(block)) {
        if (verbose)
            printf("Pro block should not be free, header = %x\n", block[0]);
        return -1;
    }       

    for (block = heap_listp + 1; block_size(block) > 0; block = block_next(block)) {
        //printf("header = %x %d\n", block[0], block[0]);
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
        if (!block_free(block) && words % 2 != 1) {
            if (verbose)
                printf("Header %x, size %d, Alloc b should be odd words\n",
                      block[0],
                      words);
            return -1;
        } else if (block_free(block) && words % 2 != 0) {
            if (verbose)
                printf("Header %x, size %d, free b should be even words\n",
                      block[0],
                      words);
            return -1;
        }

        

        //Check coalescing: no two consecutive free blocks in the heap.
        if (block_free(block)) {
            count_iter++;
            if (!in_list(block)) {
                if (verbose)
                    printf("This free block is in heap but not in list, size = %d\n",
                           block_size(block));
            }

            unsigned int next = block_size(block) + 1;        
            if (block[next] != block[0]) {
                if (verbose)
                    printf("Header and footer should be identical\n");
                return -1;
            }

            if (block_prev_free(block) || block_free(block_next(block))) {
                if (verbose)
                    printf("There should be no consecutive free blocks\n");
                return -1;
            }
        } else {
            if (block_prev_free(block_next(block)) == 1) {
                if (verbose) {
                    printf("The next block's prev_free bit is incorrect\n");

                }
                return -1;
            }
        }
    }

    if (block_free(block)) {
        if (verbose)
            printf("Epi block should not be free\n");
        return -1;
    }

    for (int i = 0; i < SEG_LIST_SIZE; ++i) {        
        if (seg_list[i] == NULL)
            continue;

        for (block = seg_list[i]; block != NULL; block = block_succ(block)) {
            count_list++;
            
            /*All next/previous pointers are consistent 
             * (if A’s next pointer points to B, B’s previous pointer
             * should point to A). */
            uint32_t *pred = block_pred(block);
            uint32_t *succ = block_succ(block);
            if (pred != NULL) {
                if (block != block_succ(pred)) {
                    if (verbose)
                        printf("List pointer is not consistent\n");
                    return -1;
                }
            }

            if (succ != NULL) {
                if (block != block_pred(succ)) {
                    if (verbose)
                        printf("List pointer is not consistent\n");
                    return -1;
                }
            }

            //All free list pointers points between mem heap lo() and hi()
            if (!in_heap(block)) {
                if (verbose)
                    printf("Block isn't in heap\n");
                return -1;
            }

            //All blocks in each list bucket fall within bucket size range
            if (find_index(block_size(block)) != i) {
                if (verbose)
                    printf("Blocks size should fall within bucket size range\n");
                return -1;                    
            }            
        }
    }

    /* Count free blocks by iterating through every block and 
     * traversing free list by pointers and see if they match. */
    //dbg_printf("Number of free blocks should be the same, "
                   //"iter = %d, list = %d;\n", count_iter, count_list);
    if (count_list != count_iter) {
    //if (1) { 
        if (verbose)
            printf("Number of free blocks should be the same, "
                   "iter = %d, list = %d;\n", count_iter, count_list);
        return -1;                    
    }

    return 0;
}
