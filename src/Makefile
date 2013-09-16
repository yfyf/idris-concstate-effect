.PHONY: Locks repl

all: Locks ConcState

Locks:
	$(MAKE) -C $@

ConcEnv.ibc: ConcEnv.idr
	idris --check $<

ConcState: ConcState.idr ConcEnv.ibc
	idris -o $@ $< -i Locks/ -p effects

repl: ConcEnv.ibc Locks
	idris -i Locks/ -p effects ConcState.idr
