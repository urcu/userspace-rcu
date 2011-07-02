#include <stdio.h>
#include <assert.h>
#include <urcu/uatomic.h>

struct testvals {
	unsigned char c;
	unsigned short s;
	unsigned int i;
	unsigned long l;
};

static struct testvals vals;

#define do_test(ptr)				\
do {						\
	__typeof__(*(ptr)) v;			\
						\
	uatomic_add(ptr, 10);			\
	assert(uatomic_read(ptr) == 10);		\
	uatomic_add(ptr, -11UL);			\
	assert(uatomic_read(ptr) == (__typeof__(*(ptr)))-1UL);	\
	v = uatomic_cmpxchg(ptr, -1UL, 22);		\
	assert(uatomic_read(ptr) == 22);		\
	assert(v == (__typeof__(*(ptr)))-1UL);	\
	v = uatomic_cmpxchg(ptr, 33, 44);		\
	assert(uatomic_read(ptr) == 22);		\
	assert(v == 22);			\
	v = uatomic_xchg(ptr, 55);			\
	assert(uatomic_read(ptr) == 55);		\
	assert(v == 22);			\
	uatomic_set(ptr, 22);			\
	uatomic_inc(ptr);			\
	assert(uatomic_read(ptr) == 23);		\
	uatomic_dec(ptr);			\
	assert(uatomic_read(ptr) == 22);		\
	v = uatomic_add_return(ptr, 74);	\
	assert(v == 96);			\
	assert(uatomic_read(ptr) == 96);	\
	uatomic_or(ptr, 58);			\
	assert(uatomic_read(ptr) == 122);	\
	v = uatomic_sub_return(ptr, 1);		\
	assert(v == 121);			\
	assert(uatomic_read(ptr) == 121);	\
	uatomic_and(ptr, 129);			\
	assert(uatomic_read(ptr) == 1);		\
} while (0)

int main(int argc, char **argv)
{
#ifdef UATOMIC_HAS_ATOMIC_BYTE
	do_test(&vals.c);
#endif
#ifdef UATOMIC_HAS_ATOMIC_SHORT
	do_test(&vals.s);
#endif
	do_test(&vals.i);
	do_test(&vals.l);
	printf("Atomic ops test OK\n");

	return 0;
}
