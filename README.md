ConcState -- an algebraic effect for managing concurrent resources in Idris
=========

This repository contains the code and report about re-implementing the eDSL
described in the "Correct-by-Construction Concurrency"[1] paper by Edwin Brady
and Kevin Hammond as an algebraic effect in the Effects[2] library of Idris.

The report PDF can be found
[here](https://github.com/yfyf/idris-concstate-effect/releases/download/1.0.0/report.pdf).

Running the code
----------------

To run the code you will need:

* Idris:

    You need Idris version `0.9.9.1` (also known to work with `0.9.9.2`, earlier version will not do).
    Easiest     way to obtain it is by installing it via cabal:

        cabal update && cabal install idris

    If you encounter problems, try the dev version of Idris and check the
    [README](https://github.com/edwinb/Idris-dev/blob/master/README).

* Unix-like OS:

    The Locks library uses `flock(2)`, which requires a Unix-like OS. So far I
    have only tested this on Linux, but in theory it should work in *BSD
    (including Mac OS) too.

* some version of `make`

If you have these then just run `make` to produce the multithreaded counter
example as an executable.

If you want to play around with the code in the Idris repl, simply do:

    cd src/
    make repl


Known issues
--------------

### Nested locks

The current `Locks` library is super simple and does not support nested locks,
so although your Idris code will typecheck, your program will simply deadlock
if you try to do nested locks.

### Non-`Int` resources

Again, `Locks` only supports `Int` resources and your code will produce
undefined behaviour for other types.

### Failing re-compilation/typechecking

Due to mysterious reasons sometimes recompilation/typechecking fails, in this
case just do `git clean -fdx` and try again.

[1]: http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.150.9865
[2]: http://www.cs.st-andrews.ac.uk/~eb/drafts/effects.pdf
