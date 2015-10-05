#include <pthread.h>


/* the lock*/
pthread_mutex_t ctr_mutex = PTHREAD_MUTEX_INITIALIZER;

/* The counter part */

int zero = 0;
int *ctr = &zero;

void reset() {
  int* ctr0 = ctr;
  *ctr0 = 0;
}

void *incr() {
   pthread_mutex_lock( &ctr_mutex );
   int* ctr0 = ctr;
   int t = *ctr0;
   *ctr0 = t +2;
   /* printf("Counter is: %d \n", *ctr); */
   pthread_mutex_unlock( &ctr_mutex );
}

int read() {
  int* ctr0 = ctr;
  int t = *ctr0;
  return t;
}

/* The threaded part */
void *thread_incr(void *arg) {
   pthread_mutex_t *thread_mutex_ptr = (pthread_mutex_t *)arg;
   incr();
   pthread_mutex_unlock( thread_mutex_ptr );
}

int  main(void)
{
  
   /* ctr = 0 */
   reset();
   int rc1;
   pthread_mutex_t thread_mutex = PTHREAD_MUTEX_INITIALIZER;
   pthread_mutex_lock( &thread_mutex );
   pthread_t thread1;
   /* Spawn */
   rc1=pthread_create( &thread1, NULL, thread_incr, &thread_mutex);
   
   /*Local incr */
   incr();

   /*JOIN */
   pthread_mutex_lock( &thread_mutex );
   /* printf("I'm done with a final counter of: %d\n", *ctr); */
    
   int t = read();
   return t;
}
