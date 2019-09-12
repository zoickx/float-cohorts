# flocq-cohorts
Simple value-preserving operations on floats in Coq (Flocq)

## Abstract
Any binary floating-point number is, in essence, a pair `(m, e)` serving as a representation of a real number `r = m * 2^e`.
Such a representation is not unique. For example, `0.5 = 1 * 2^(-1) = 2 * 2^(-2) = ...`, thus having representations `(1, -1)`, `(2, -2)` and so on.

A **cohort** is the set of all representations of a given real number.
That is, for `r : R` its cohort would be the set `{(m, e) | m * 2^e = r}`.
This project defines a number of operations on floats, which do not change their cohort and therefore preserve the exact value of the real number they represent

## Motivation
Floating-point operations are most often performed with rounding, and an extensive foundation for that is provided in Flocq. However, for converting between standard formats (for example, `binary64` -> `binary32`) it can be important to know if the conversion is performed *with no loss of precision*. I was unable to find an easy way to perform such a check in Flocq and thus this project was born.

## Key features
* Decidable equality on floats with no dependency on `R` ([FloatEqb.v](FloatEqb.v))
* Value-preserving operations to shift a float "up"/"down" in a cohort ([BinaryCohorts.v](BinaryCohorts.v))
* Converting an arbitrary float into an IEEE-754-normalized form without loss of precision ([B754Exact.v](B754Exact.v))

## Building
Install prerequisites:
``` shell
opam repo add coq-released http://coq.inria.fr/opam/released
opam install coq coq-flocq
```

Clone and build:
``` shell
git clone https://github.com/zoickx/flocq-cohorts 
cd flocq-cohorts
make -j
```
