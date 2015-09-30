#include <pthread.h>

void *incr();

pthread_mutex_t mutex1 = PTHREAD_MUTEX_INITIALIZER;
int  counter = 0;

int  main(void)
{
   int rc1, rc2;
   
   pthread_t thread1, thread2;

   rc1=pthread_create( &thread1, NULL, &incr, NULL);

   rc2=pthread_create( &thread2, NULL, &incr, NULL);
   pthread_join( thread1, NULL);
   pthread_join( thread2, NULL); 

   return 1;
}

void *incr()
{
   pthread_mutex_lock( &mutex1 );
   counter++;
   pthread_mutex_unlock( &mutex1 );
}
