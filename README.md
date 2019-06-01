# cbc-casper-proof
Proofs of properties of CBC Casper

See [Refinement and Verification of CBC Casper](https://eprint.iacr.org/2019/415.pdf)

## Resources
- [CBC Casper paper](https://github.com/cbc-casper/cbc-casper-paper)
- [Isabelle proofs for the old version of CBC Casper](https://github.com/pirapira/cbc_casper)

## Create documentation

### Preparations

Document creation requires `isabelle` as a command line tool. Make sure you have `isabelle` in your `$PATH` or set an `alias`.

Make sure you have a suitable `texlive` environment installed. Otherwise, LaTeX builds will fail.

### Quick build

Run the build command from a terminal with:
```
isabelle build -D Isabelle
```

For reference see also the [Isabelle tutorial](http://www21.in.tum.de/~nipkow/LNCS2283/).

