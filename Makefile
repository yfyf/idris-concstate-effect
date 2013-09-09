.PHONY: report code

all: report code

report:
	$(MAKE) -C $@
	ln -sf $@/$@.pdf

code:
	$(MAKE) -C src/
