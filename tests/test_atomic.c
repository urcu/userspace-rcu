#include <stdio.h>
#include <arch_atomic.h>
#include <assert.h>

struct testvals {
	unsigned char c;
	unsigned short s;
	unsigned int i;
	unsigned long l;
};

static struct testvals vals;

int main(int argc, void **argv)
{
	atomic_add(&vals.c, 10);
	assert(vals.c == 10);
	atomic_add(&vals.c, -11);
	assert((char)vals.c == -1);
}
