
test_urcu: urcu.o test_urcu.c
	gcc -g -o test_urcu urcu.o test_urcu.c

urcu.o: urcu.c urcu.h
	gcc -g -o urcu.o urcu.c
