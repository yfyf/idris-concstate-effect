.PHONY: Locks

all: Locks ConcState

Locks:
	$(MAKE) -C $@

ConcEnv.ibc: ConcEnv.idr
	idris --check $<

ConcState: ConcState.idr ConcEnv.ibc
	idris -o $@ $< -i Locks/ -p effects

