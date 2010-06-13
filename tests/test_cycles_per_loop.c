#include <urcu/arch.h>
#include <stdio.h>

#define NR_LOOPS 1000000UL

static inline void loop_sleep(unsigned long l)
{
	while(l-- != 0)
		cpu_relax();
}

int main()
{
	cycles_t time1, time2;

	time1 = get_cycles();
	loop_sleep(NR_LOOPS);
	time2 = get_cycles();
	printf("CPU clock cycles per loop: %g\n", (time2 - time1) /
						  (double)NR_LOOPS);
}
