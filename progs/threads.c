#include <stdlib.h>
#include <pthread.h>
#include "threads.h"

/* gcc -Wall -pthread */

lock_t new_lock() {
  return (lock_t)malloc(sizeof(pthread_mutex_t));
}

void make_lock(lock_t lock) {
  pthread_mutex_init((pthread_mutex_t*)lock, NULL);
  pthread_mutex_lock((pthread_mutex_t*)lock);
}

void free_lock(lock_t lock) {
  pthread_mutex_destroy((pthread_mutex_t*)lock);
  return;
}

void acquire(lock_t lock) {
  pthread_mutex_lock((pthread_mutex_t*)lock);
  return;
}

void release(lock_t lock) {
  pthread_mutex_unlock((pthread_mutex_t*)lock);
  return;
}

void spawn_thread(void* (*f)(void*), void* args) {
  pthread_t *t = (pthread_t*)malloc(sizeof(pthread_t));
  pthread_create(t, NULL, f, args);
  return;
}

void exit_thread(void) {
  pthread_exit(NULL);
  return;
}
