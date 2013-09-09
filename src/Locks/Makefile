all: Locks.ibc

Locks.ibc: Locks.idr locker
	idris --check $<

locker: locker.c
	gcc -Wall -c -o $@ $<
