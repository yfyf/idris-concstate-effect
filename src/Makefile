.PHONY: ConcState Locks

all: Locks ConcEnv ConcState

Locks:
	$(MAKE) -C $@

ConcEnv: ConcEnv.idr
	idris --check $<

ConcState: ConcState.idr
	idris -o $@ $< -i Locks/ -p effects

