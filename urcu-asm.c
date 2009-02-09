#include "urcu.h"

void show_read_lock(void)
{
	asm volatile ("/* start */");
	rcu_read_lock();
	asm volatile ("/* end */");
}

void show_read_unlock(void)
{
	asm volatile ("/* start */");
	rcu_read_unlock();
	asm volatile ("/* end */");
}
