
all: locker Locks

locker: locker.c
	gcc -Wall -c -o locker $<

Locks: Locks.idr
	idris -o Locks $<
