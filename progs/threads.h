typedef void* lock_t;
typedef void* cond_t;

lock_t new_lock(void);

void make_lock(lock_t lock);

void free_lock(lock_t lock);

void acquire(lock_t lock);

void release(lock_t lock);

void spawn_thread(void* (*f)(void*), void* args);

void exit_thread(void);

void wait(cond_t cv, lock_t lock);

void signal(cond_t cv);
