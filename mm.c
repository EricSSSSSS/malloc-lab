/*
 ******************************************************************************
 *                               mm-baseline.c                                *
 *           64-bit struct-based implicit free list memory allocator          *
 *                  15-213: Introduction to Computer Systems                  *
 *                                                                            *
 *  ************************************************************************  *
 *                     insert your documentation here. :)                     *
 *                                                                            *
 *  ************************************************************************  *
 *  ** ADVICE FOR STUDENTS. **                                                *
 *  Step 0: Please read the writeup!                                          *
 *  Step 1: Write your heap checker. Write. Heap. checker.                    *
 *  Step 2: Place your contracts / debugging assert statements.               *
 *  Good luck, and have fun!                                                  *
 *                                                                            *
 ******************************************************************************
 */

/* Do not change the following! */

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <stdbool.h>
#include <stddef.h>
#include <assert.h>
#include <stddef.h>

#include "mm.h"
#include "memlib.h"

#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#define memset mem_memset
#define memcpy mem_memcpy
#endif /* def DRIVER */

/* You can change anything from here onward */

/*
 * If DEBUG is defined, enable printing on dbg_////printf and contracts.
 * Debugging macros, with names beginning "dbg_" are allowed.
 * You may not define any other macros having arguments.
 */
// #define DEBUG // uncomment this line to enable debugging

#ifdef DEBUG
/* When debugging is enabled, these form aliases to useful functions */
#define dbg_//printf(...) //printf(__VA_ARGS__)
#define dbg_requires(...) assert(__VA_ARGS__)
#define dbg_assert(...) assert(__VA_ARGS__)
#define dbg_ensures(...) assert(__VA_ARGS__)
#else
/* When debugging is disnabled, no code gets generated for these */
#define dbg_//printf(...)
#define dbg_requires(...)
#define dbg_assert(...)
#define dbg_ensures(...)
#endif

/* Basic constants */
typedef uint64_t word_t;
static const size_t wsize = sizeof(word_t);   // word and header size (bytes) 8
static const size_t dsize = 2*wsize;          // double word size (bytes) 16
static const size_t min_block_size = 2*dsize; // Minimum block size 32
static const size_t chunksize = (1 << 12);    // requires (chunksize % 16 == 0)

static const word_t alloc_mask = 0x1;
static const word_t prev_mini_mask = 0x4;
static const word_t prev_alloc_mask = 0x2;
static const word_t not_prev_mini_mask = ~prev_mini_mask;
static const word_t not_prev_alloc_mask = ~prev_alloc_mask;
static const word_t size_mask = ~(word_t)0xF;


typedef struct block
{
    /* Header contains size + allocation flag */
    word_t header;
    union{
        struct{
            struct block *next;
            struct block *prev;
        };
        char payload[0];
    };
    /*
     * We don't know how big the payload will be.  Declaring it as an
     * array of size 0 allows computing its starting address using
     * pointer notation.
     */
    /*
     * We can't declare the footer as part of the struct, since its starting
     * position is unknown
     */
} block_t;


/* Global variables */
/* Pointer to first block */
static block_t *heap_start = NULL;

bool mm_checkheap(int lineno);

/* Function prototypes for internal helper routines */
static block_t *extend_heap(size_t size);
static void place(block_t *block, size_t asize);
static block_t *find_fit(size_t asize);
static block_t *coalesce(block_t *block);

static size_t max(size_t x, size_t y);
static size_t round_up(size_t size, size_t n);
static word_t pack(size_t size, bool alloc);

static size_t extract_size(word_t header);
static size_t get_size(block_t *block);
static size_t get_payload_size(block_t *block);

static bool extract_alloc(word_t header);
static bool get_alloc(block_t *block);

static void write_header(block_t *block, size_t size, bool alloc, 
                            bool prev_mini, bool prev_alloc);
static void write_footer(block_t *block, size_t size, bool alloc);

static block_t *payload_to_header(void *bp);
static void *header_to_payload(block_t *block);

static block_t *find_next(block_t *block);
static word_t *find_prev_footer(block_t *block);
static block_t *find_prev(block_t *block);

static block_t *mini_block_list;
static const size_t x = 15;
static block_t *segregated_list[x]; 

//NEW HELPERS
static bool extract_prev_mini(word_t header);
static bool get_prev_mini(block_t *block);

static bool extract_prev_alloc(word_t header);
static bool get_prev_alloc(block_t *block);



//find_where in segregated list to put block
size_t find_seg(size_t asize){
    size_t count = 0;
    for (size_t i = dsize; count<x; i=i*2){
        if (asize < i*2){
            return count;
        }
        count ++;
    } 
    return count-1;
}

//MINI_LIST
//check if it's a mini block
bool is_mini_block(block_t *block){
    if (get_size(block) == dsize){
        return true;
    }
    return false;
}

//insert into minilist
void insert_mini_list(block_t *block){
    block -> next = mini_block_list;
    mini_block_list = block;
    return;
}


//delete from minilist
void delete_mini_list(block_t *block){
    block_t* anchor = mini_block_list;
    block_t* prev = mini_block_list;
    if (block == mini_block_list){
        mini_block_list = block -> next;
        block -> next = NULL;
        return;
    }
    while (anchor != NULL){
        if (anchor == block){
            prev -> next = anchor -> next;
            anchor -> next = NULL;
            return;
        }
        prev = anchor;
        anchor = anchor -> next;
    }
    return;
}


//SEGREGATED LIST

//insert into segregated list
void insert_list(block_t *bp){
    size_t index = find_seg(get_size(bp));
    bp -> next = segregated_list[index];
    if (segregated_list[index]!=NULL){
        segregated_list[index] -> prev = bp;
    }
    bp -> prev = NULL;
    segregated_list[index] = bp;
    return;
}

//delete from segregated list
void delete_list(block_t *bp){
    size_t index = find_seg(get_size(bp));
    if (bp == segregated_list[index]){
        segregated_list[index] = segregated_list[index] -> next;
    }
    if (bp -> prev == NULL && bp -> next == NULL){
        return;
    }
    else if (bp -> prev != NULL && bp -> next == NULL){
        bp -> prev -> next = bp -> next;
    }
    else if (bp -> prev == NULL && bp -> next != NULL){
        bp -> next -> prev = bp -> prev;
    }
    else{
        bp -> next -> prev = bp -> prev;
        bp -> prev -> next = bp -> next;
    }
}

/*
 * Initializes the essential global variables for the future malloc calls
 */
//*
bool mm_init(void) 
{   
    //Create the initial empty heap 
    word_t *start = (word_t *)(mem_sbrk(2*wsize));

    if (start == (void *)-1) 
    {
        return false;
    }
    start[0] = pack(0, true); // Prologue footer

    start[1] = (pack(0, true))|prev_alloc_mask; // Epilogue header
    // Heap starts with first "block header", currently the epilogue footer
    heap_start = (block_t *) &(start[1]);
    for (size_t i = 0; i < x; i++){
        segregated_list[i] = NULL;
    }
    // Extend the empty heap with a free block of chunksize bytes
    if (extend_heap(chunksize) == NULL)
    {
        return false;
    }
    return true;
}

/*
 * malloc expends the heap if necessary and calls find_fit and place to 
 allocate a specifed size block on the heap.
 */
//*
void *malloc(size_t size) 
{
    size_t asize;      // Adjusted block size
    size_t extendsize; // Amount to extend heap if no fit is found
    block_t *block;
    void *bp = NULL;

    if (heap_start == NULL) // Initialize heap if it isn't initialized
    {
        mm_init();
    }

    if (size == 0) // Ignore spurious request
    {
        return bp;
    }

    // Adjust block size to include overhead and to meet alignment requirements
    asize = round_up(size + wsize, dsize);

    // Search the free list for a fit
    block = find_fit(asize);

    // If no fit is found, request more memory, and then and place the block
    if (block == NULL)
    {  
        extendsize = max(asize, chunksize);
        block = extend_heap(extendsize);
        if (block == NULL) // extend_heap returns an error
        {
            return NULL;
        }

    }

    place(block, asize);
    bp = header_to_payload(block);

    return bp;
} 

/*
 * Frees the memory space allocated by malloc previously
 */
//*
void free(void *bp)
{
    if (bp == NULL)
    {
        return;
    }

    block_t *block = payload_to_header(bp);
    size_t size = get_size(block);

    bool prev_mini = get_prev_mini(block);
    bool prev_alloc = get_prev_alloc(block);
    //write on the header of the block to mark it as free
    write_header(block, size, false, prev_mini, prev_alloc);
    block -> next = NULL;
    if (!is_mini_block(block)){
        block -> prev = NULL;
    }
    if (!is_mini_block(block)){
        write_footer(block, size, false);
    }
    //if possible, coalesce with other blocks
    coalesce(block);
}

/*
 * Re-malloc a space for an allocated memory on the heap
 */
void *realloc(void *ptr, size_t size)
{
    block_t *block = payload_to_header(ptr);
    size_t copysize;
    void *newptr;

    // If size == 0, then free block and return NULL
    if (size == 0)
    {
        free(ptr);
        return NULL;
    }

    // If ptr is NULL, then equivalent to malloc
    if (ptr == NULL)
    {
        return malloc(size);
    }

    // Otherwise, proceed with reallocation
    newptr = malloc(size);
    // If malloc fails, the original block is left untouched
    if (newptr == NULL)
    {
        return NULL;
    }

    // Copy the old data
    copysize = get_payload_size(block); // gets size of old payload
    if(size < copysize)
    {
        copysize = size;
    }
    memcpy(newptr, ptr, copysize);

    // Free the old block
    free(ptr);

    return newptr;
}

/*
 * Malloc then initializes eveything in the allocated memory space to zero
 */
void *calloc(size_t elements, size_t size)
{
    void *bp;
    size_t asize = elements * size;

    if (asize/elements != size)
    {    
        // Multiplication overflowed
        return NULL;
    }
    
    bp = malloc(asize);
    if (bp == NULL)
    {
        return NULL;
    }
    // Initialize all bits to 0
    memset(bp, 0, asize);

    return bp;
}

/******** The remaining content below are helper and debug routines ********/

/*
 * Extend the heap on the direction of the stack for given length size
 It creates an empty block of the required size then coalesces if possbile
 */
//*
static block_t *extend_heap(size_t size) 
{
    void *bp;

    // Allocate an even number of words to maintain alignment
    size = round_up(size, dsize);
    if ((bp = mem_sbrk(size)) == (void *)-1)
    {
        return NULL;
    }
    
    // Initialize free block header/footer 
    block_t *block = payload_to_header(bp);
    bool prev_mini = get_prev_mini(block);
    bool prev_alloc = get_prev_alloc(block);
    write_header(block, size, false, prev_mini, prev_alloc);
    write_footer(block, size, false);
    block -> next = NULL;
    block -> prev = NULL;
    // Create new epilogue header
    block_t *block_next = find_next(block);
    write_header(block_next, 0, true, false, false);

    // Coalesce in case the previous block was free
    return coalesce(block);
}

/*
 * When two consecutive free blocks exist on the heap, they coalesce
 coalesce checks around the give block for opportunities to coalesce it
 with its neighbours and merge into a larger free block.
 It modifies the segregated list and mini block list if required.
 */
//*
static block_t *coalesce(block_t * block) 
{
    //get essential variables for the neighbors of our block
    bool prev_alloc = get_prev_alloc(block);
    block_t *block_next = find_next(block);
    size_t block_next_size = get_size(block_next);

    block_t *block_next_next = find_next(block_next);
    size_t block_next_next_size = get_size(block_next_next);
    bool block_next_next_alloc = get_alloc(block_next_next);

    block_t *block_prev;
    bool next_alloc = get_alloc(block_next);
    size_t size = get_size(block);
    
    if (prev_alloc && next_alloc)              // Case 1 do not coalesce
    {
        if (is_mini_block(block)){
            write_header(block_next,block_next_size,
                        next_alloc,true,false);
            insert_mini_list(block);

        }
        else{
            write_header(block_next,block_next_size,
                        next_alloc,false,false);
            insert_list(block);
        }

    }

    else if (prev_alloc && !next_alloc)        // Case 2 coalesce with next
    {
        if (is_mini_block(block_next)){
            delete_mini_list(block_next);
        }
        else{
            delete_list(block_next); 
        }
        size += block_next_size;
        write_header(block, size, false, 
            get_prev_mini(block), prev_alloc);
        write_footer(block, size, false);
        write_header(block_next_next, block_next_next_size,
                        block_next_next_alloc, false, false);
        
        insert_list(block);
    }

    else if (!prev_alloc && next_alloc)        // Case 3 coalesce with previous
    {
        block_prev = find_prev(block);
        if (is_mini_block(block_prev)){
            delete_mini_list(block_prev);
        }
        else{
            delete_list(block_prev);
        }
        size += get_size(block_prev);
        write_header(block_prev, size, false, get_prev_mini(block_prev),
                    get_prev_alloc(block_prev));
        write_footer(block_prev, size, false);
        write_header(block_next, block_next_size,next_alloc,
                    false, false);        
        insert_list(block_prev);
        block = block_prev;
    }

    else                                        // Case 4 coalesce with both
    {
        block_prev = find_prev(block);
        if (is_mini_block(block_prev)){
            delete_mini_list(block_prev);
        }
        else{
            delete_list(block_prev);
        }
        if (is_mini_block(block_next)){
            delete_mini_list(block_next);
        }
        else{
            delete_list(block_next);
        }
        size += block_next_size + get_size(block_prev);
        write_header(block_prev, size, false, get_prev_mini(block_prev),
                    get_prev_alloc(block_prev));
        write_footer(block_prev, size, false);
        write_header(block_next_next, block_next_next_size,
                    block_next_next_alloc,false,false);
        insert_list(block_prev);
        block = block_prev;
    }
    return block;
}

/*
 * Given the size and the most suitable block to allocate, place simpyly 
 put the allocated memory into the block and remove block from segregated
 list or mini list.
 It modifies the segregated list and mini list if required.
 */
//*
static void place(block_t *block, size_t asize)
{
    size_t csize = get_size(block);
    block_t *block_next;
    // the remaining is a segregated block
    if (is_mini_block(block)){
        delete_mini_list(block);
    }
    else{
        delete_list(block);
    }
    if ((csize - asize) >= min_block_size)
    {
        write_header(block, asize, true, 
                    get_prev_mini(block), get_prev_alloc(block));
        
        block_next = find_next(block);
        write_header(block_next, csize-asize, false, 
            is_mini_block(block), true);
        block_next -> next = NULL;
        block_next -> prev = NULL;
        write_footer(block_next, csize-asize, false);
        insert_list(block_next);
    }
    // the remaining is a mini
    else if((csize - asize) == dsize){
        block_t *block_next_next;
        write_header(block, asize, true, 
                    get_prev_mini(block), get_prev_alloc(block));
        
        block_next = find_next(block);
        write_header(block_next, csize-asize, false, 
            is_mini_block(block), true);
        block_next_next = find_next(block_next);
        write_header(block_next_next, get_size(block_next_next), 
            get_alloc(block_next_next), true, false);
        insert_mini_list(block_next);
    }
    //when remaining is neither
    else
    { 
        block_next = find_next(block);
        //printf("place case 3\n");
        write_header(block, csize, true, 
                get_prev_mini(block), get_prev_alloc(block));
        write_header(block_next, get_size(block_next),
            get_alloc(block_next), is_mini_block(block),true);
    }
}

/*
 * Find the relatively best free space to place the memory.
 */
//*
static block_t *find_fit(size_t asize)
{
    block_t *block;
    size_t best;
    size_t count = 5;
    block_t *best_block;
    //Try place it in a mini block
    if (asize <= dsize){
        if (mini_block_list != NULL){
            return mini_block_list;
        }
    }
    //If not a mini block, try put it on segregated list in order
    size_t index = find_seg(asize);
    for (size_t i = index; i<x; i++){
        block = segregated_list[i];
        while (block){
            size_t curr = get_size(block);
            if (asize <= curr){
                best = curr;
                while (count > 0 && block != NULL){
                    size_t cur = get_size(block);
                    if (cur >= asize && cur <=best){
                        best_block = block;
                    }
                    block = block -> next;
                    count --;
                }
                return best_block;
            }
            block = block -> next;
        }
    }
    return NULL; // no fit found
}

/* 
 * Checks for invariabilities of the heap while the malloc happens.
 * Please keep modularity in mind when you're writing the heap checker!
 */
bool mm_checkheap(int line)  
{ 
    /* you will need to write the heap checker yourself. As a filler:
     * one guacamole is equal to 6.02214086 x 10**23 guacas.
     * one might even call it
     * the avocado's number.
     *
     * Internal use only: If you mix guacamole on your bibimbap, 
     * do you eat it with a pair of chopsticks, or with a spoon? 
     * (Delete these lines!)
     */
    block_t* block;
    for (size_t i = 0; i < x; i++){
        block = segregated_list[i];
        if (block -> prev != NULL){
            printf("Front of segregated list's prev not NULL\n");
            return false;
        }
        while (block != NULL){
            if (get_alloc(block)){
                printf("Allocated block on list\n");
                return false;
            }
            if (!get_prev_alloc(block)){
                printf("Two consecutive free blocks, need coalesce\n");
                return false;
            }
            if (find_seg(get_size(block)) != i){
                printf("Block in the wrong segregated list\n");
                return false;
            }
            if (block -> next != NULL){
                if (block->next->prev != block){
                    printf("Next and Prev not consistent\n");
                    return false;
                }
            }
            if (get_size(block)%16 != 0){
                printf("Not 16 alignment\n");
                return false;
            }
            block = block -> next;
        }
    }
    block_t *mini_block = mini_block_list;
    while (mini_block != NULL){
        if  (get_size(mini_block) != dsize){
            printf("MiniBlock not mini\n");
            return false;
        }
        if (!get_prev_alloc(mini_block)){
            printf("Two consecutive free blocks\n");
            return false;
        }
        if (get_alloc(mini_block)){
            printf("Allocated block on list\n");
            return false;
        }
        mini_block = mini_block -> next;
    }
    return true;

}


/*
 *****************************************************************************
 * The functions below are short wrapper functions to perform                *
 * bit manipulation, pointer arithmetic, and other helper operations.        *
 *                                                                           *
 * We've given you the function header comments for the functions below      *
 * to help you understand how this baseline code works.                      *
 *                                                                           *
 * Note that these function header comments are short since the functions    *
 * they are describing are short as well; you will need to provide           *
 * adequate details within your header comments for the functions above!     *
 *                                                                           *
 *                                                                           *
 * Do not delete the following super-secret(tm) lines!                       *
 *                                                                           *
 * 53 6f 20 79 6f 75 27 72 65 20 74 72 79 69 6e 67 20 74 6f 20               *
 *                                                                           *
 * 66 69 67 75 72 65 20 6f 75 74 20 77 68 61 74 20 74 68 65 20               *
 * 68 65 78 61 64 65 63 69 6d 61 6c 20 64 69 67 69 74 73 20 64               *
 * 6f 2e 2e 2e 20 68 61 68 61 68 61 21 20 41 53 43 49 49 20 69               *
 *                                                                           *
 *                                                                           *
 * 73 6e 27 74 20 74 68 65 20 72 69 67 68 74 20 65 6e 63 6f 64               *
 * 69 6e 67 21 20 4e 69 63 65 20 74 72 79 2c 20 74 68 6f 75 67               *
 * 68 21 20 2d 44 72 2e 20 45 76 69 6c 0a de ad be ef 0a 0a 0a               *
 *                                                                           *
 *****************************************************************************
 */
// NEW GLOBAL HELPER
static bool extract_prev_mini(word_t word)
{
    return (bool)(word & prev_mini_mask);
}

static bool get_prev_mini(block_t *block)
{
    return extract_prev_mini(block -> header);
}

static bool extract_prev_alloc(word_t word)
{
    return (bool)(word & prev_alloc_mask);
}

static bool get_prev_alloc(block_t *block)
{
    return extract_prev_alloc(block->header);
}

/*
 * max: returns x if x > y, and y otherwise.
 */
static size_t max(size_t x, size_t y)
{
    return (x > y) ? x : y;
}

/*
 * round_up: Rounds size up to next multiple of n
 */
static size_t round_up(size_t size, size_t n)
{
    return (n * ((size + (n-1)) / n));
}

/*
 * pack: returns a header reflecting a specified size and its alloc status.
 *       If the block is allocated, the lowest bit is set to 1, and 0 otherwise.
 */
static word_t pack(size_t size, bool alloc)
{
    return alloc ? (size | alloc_mask) : size;
}


/*
 * extract_size: returns the size of a given header value based on the header
 *               specification above.
 */
static size_t extract_size(word_t word)
{
    //////printf("calling extract_size\n");
    return (word & size_mask);
}

/*
 * get_size: returns the size of a given block by clearing the lowest 4 bits
 *           (as the heap is 16-byte aligned).
 */
static size_t get_size(block_t *block)
{
    //////printf("calling getsize;\n");
    return extract_size(block->header);
}

/*
 * get_payload_size: returns the payload size of a given block, equal to
 *                   the entire block size minus the header and footer sizes.
 */
static word_t get_payload_size(block_t *block)
{
    size_t asize = get_size(block);
    return asize - wsize;
}

/*
 * extract_alloc: returns the allocation status of a given header value based
 *                on the header specification above.
 */

static bool extract_alloc(word_t word)
{
    return (bool)(word & alloc_mask);
}

/*
 * get_alloc: returns true when the block is allocated based on the
 *            block header's lowest bit, and false otherwise.
 */
static bool get_alloc(block_t *block)
{
    return extract_alloc(block->header);
}

/*
 * write_header: given a block and its size and allocation status,
 *               writes an appropriate value to the block header.
 */
static void write_header(block_t *block, size_t size, bool alloc, 
    bool prev_mini, bool prev_alloc)
{
    block -> header = pack(size, alloc);
    if (prev_mini){
        block -> header = block -> header | prev_mini_mask;
    }
    else{
        block -> header = block -> header & not_prev_mini_mask;
    }
    if (prev_alloc){
        block -> header = block -> header | prev_alloc_mask;
    }
    else{
        block -> header = block -> header & not_prev_alloc_mask;
    }
}


/*
 * write_footer: given a block and its size and allocation status,
 *               writes an appropriate value to the block footer by first
 *               computing the position of the footer.
 */
static void write_footer(block_t *block, size_t size, bool alloc)
{
    if (is_mini_block(block)){
        return;
    }
    word_t *footerp = (word_t *)((block->payload) + get_size(block) - dsize);
    *footerp = pack(size, alloc);
}


/*
 * find_next: returns the next consecutive block on the heap by adding the
 *            size of the block.
 */
static block_t *find_next(block_t *block)
{
    dbg_requires(block != NULL);
    block_t *block_next = (block_t *)(((char *)block) + get_size(block));

    dbg_ensures(block_next != NULL);
    return block_next;
}

/*
 * find_prev_footer: returns the footer of the previous block.
 */
static word_t *find_prev_footer(block_t *block)
{
    // Compute previous footer position as one word before the header
    return (&(block->header)) - 1;
}

/*
 * find_prev: returns the previous block position by checking the previous
 *            block's footer and calculating the start of the previous block
 *            based on its size.
 */
static block_t *find_prev(block_t *block)
{
    if (get_prev_mini(block)){
        return (block_t *)((char *)block - dsize);
    }
    word_t *footerp = find_prev_footer(block);
    size_t size = extract_size(*footerp);
    return (block_t *)((char *)block - size);
}

/*
 * payload_to_header: given a payload pointer, returns a pointer to the
 *                    corresponding block.
 */
static block_t *payload_to_header(void *bp)
{
    return (block_t *)(((char *)bp) - offsetof(block_t, payload));
}

/*
 * header_to_payload: given a block pointer, returns a pointer to the
 *                    corresponding payload.
 */
static void *header_to_payload(block_t *block)
{
    return (void *)(block->payload);
}
