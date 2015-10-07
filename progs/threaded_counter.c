/*#include <stdio.h>
 */
#include <pthread.h>
#include "threads.h"

/* the lock*/
lock_t ctr_lock;

/* The counter part */

int zero = 0;
int *ctr = &zero;

void reset() {
  int* ctr0 = ctr;
  *ctr0 = 0;
}

void incr() {
  /* acquire( &ctr_lock ); */
   int* ctr0 = ctr;
   int t = *ctr0;
   *ctr0 = t +1;
   /* printf("Counter is: %d \n", *ctr);
    */
}

int read() {
  int* ctr0 = ctr;
  int t = *ctr0;
  return t;
}

/* The threaded part */

void concurrent_incr() {
  lock_t *ctr_lock_ptr = &ctr_lock; 
  acquire(ctr_lock_ptr);
  incr();
  release(ctr_lock_ptr);
}

void *thread_func(void *arg) {
  lock_t *thread_mutex_ptr;
  thread_mutex_ptr = (lock_t *)arg;
   concurrent_incr();
   release( thread_mutex_ptr );
   return NULL;
}

int  main(void)
{
   /* ctr = 0 */
   reset();
   makelock(&ctr_lock);
   release(&ctr_lock);
   lock_t thread_mutex;
   makelock(&thread_mutex);
   /* Spawn */
   spawn_thread(&thread_func, (void*)&thread_mutex);
   /*rc1=pthread_create( &thread1, NULL, thread_incr, &thread_mutex); */
   
   /*Local incr */
   concurrent_incr();

   /*JOIN */
   acquire( &thread_mutex );
   /* printf("I'm done with a final counter of: %d\n", *ctr);
    */ 
   int t = read();
   return t;
}
