
test_urcu: urcu.o test_urcu.c
	gcc -Wall -lpthread -g -o test_urcu urcu.o test_urcu.c

urcu.o: urcu.c urcu.h
	gcc -Wall -lpthread -g -c -o urcu.o urcu.c

.PHONY: clean

clean:
	rm -f urcu.o test_urcu
