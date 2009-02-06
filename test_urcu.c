#include <stdio.h>
#include <pthread.h>
#include <stdlib.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>
#include <stdio.h>
#include "urcu.h"

#define NR_READ 10
#define NR_WRITE 4


void *thr_reader(void *arg)
{
	printf("thread %s, thread id : %lu, pid %lu\n",
			"reader", pthread_self(), getpid());
	sleep(2);

	urcu_register_thread();



	urcu_unregister_thread();
	return ((void*)1);

}

void *thr_writer(void *arg)
{
	int i;

	printf("thread %s, thread id : %lu, pid %lu\n",
			"writer", pthread_self(), getpid());
	sleep(2);

	for (i = 0; i < 1000; i++) {
	}

	return ((void*)2);
}

int main()
{
	int err;
	pthread_t tid_reader[NR_READ], tid_writer[NR_WRITE];
	void *tret;
	int i;

	for (i = 0; i < NR_READ; i++) {
		err = pthread_create(&tid_reader[i], NULL, thr_reader, NULL);
		if (err != 0)
			exit(1);
	}
	for (i = 0; i < NR_WRITE; i++) {
		err = pthread_create(&tid_writer[i], NULL, thr_writer, NULL);
		if (err != 0)
			exit(1);
	}

	sleep(10);

	for (i = 0; i < NR_WRITE; i++) {
		err = pthread_join(tid_reader[i], &tret);
		if (err != 0)
			exit(1);
	}
	for (i = 0; i < NR_WRITE; i++) {
		err = pthread_join(tid_writer[i], &tret);
		if (err != 0)
			exit(1);
	}

	return 0;
}
