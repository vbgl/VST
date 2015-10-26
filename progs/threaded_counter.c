/*#include <stdio.h>
 */
#include <pthread.h>
#include "threads.h"
/*#include <stdio.h>*/
#include <stdlib.h>

/* the lock*/
lock_t ctr_lock;

/* context structure */
struct ctr_context {
  lock_t thread_lock ;
  lock_t ctr_lock ;
  int *ctr;
};

/* The counter part */

void reset(int *ctr) {
  *ctr = 0;
}

void incr(int *ctr) {
  /* acquire( &ctr_lock ); */
   int t = *ctr;
   *ctr = t + 1;
   /*printf("Counter is: %d \n", *ctr); */
    
}

int read(int *ctr) {
  int* ctr0 = ctr;
  int t = *ctr0;
  return t;
}

/* The threaded part */

/* void concurrent_incr(int *ctr, lock_t *ctr_lock_ptr) {
  acquire(ctr_lock_ptr);
  incr(ctr);
  release(ctr_lock_ptr);
  } */

void* thread_func(void *context) {
  struct ctr_context *ctr_context = (struct ctr_context*)context;
  lock_t *thread_lock_ptr = &ctr_context->thread_lock;
  lock_t *ctr_lock_ptr = &ctr_context->ctr_lock;
  int *ctr;
  //Increment the counter
  acquire(ctr_lock_ptr);
  ctr = ctr_context->ctr;
  incr(ctr);
  release(ctr_lock_ptr);
  //Yield: 'ready to join'.
  release( thread_lock_ptr );
  return NULL;
}

int  main(void)
{
  struct ctr_context *ctr_context = (struct ctr_context*)malloc(sizeof(struct ctr_context));
  lock_t *thread_lock_ptr = &ctr_context->thread_lock;
  lock_t *ctr_lock_ptr = &ctr_context->ctr_lock;
  int *ctr = (int *)malloc(sizeof(int));
  ctr_context->ctr = ctr;
  reset(ctr); //ctr = 0
  makelock(ctr_lock_ptr);
   release(ctr_lock_ptr);
   makelock(thread_lock_ptr);
   /* Spawn */
   spawn_thread((void *)&thread_func, (void*)ctr_context); 
   /*rc1=pthread_create( &thread1, NULL, thread_incr, &thread_mutex); */
   
  //Increment the counter
   acquire(ctr_lock_ptr);
   ctr = ctr_context->ctr;
   incr(ctr);
   release(ctr_lock_ptr);

   /*JOIN */
   acquire( thread_lock_ptr );
   
   /*En concurrency */
   acquire( ctr_lock_ptr );
   /*printf("I'm done with a final counter of: %d\n", *ctr);*/

   /* Should free this locks */
   
   ctr = ctr_context->ctr;
   int t = read(ctr);
   return t;
}
