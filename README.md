# float-cohorts
Simple value-preserving operations on floats in Coq

## Abstract
Any binary floating-point number is, in essence, a pair `(m, e)` serving as a representation of a real number `r = m * 2^e`.
Such a representation is not unique. For example, `0.5 = 1 * 2^(-1) = 2 * 2^(-2) = ...`, thus having representations `(1, -1)`, `(2, -2)` and so on.

A **cohort** is the set of all representations of a given real number.
That is, for `r : R` its cohort would be the set `{(m, e) | m * 2^e = r}`.
This project defines a number of operations on floats, which do not change their cohort and therefore preserve the exact value of the real number they represent

## Motivation
Floating-point operations are most often performed with rounding, and an extensive foundation for that is provided in [Flocq](http://flocq.gforge.inria.fr/). However, for converting between standard formats (for example, `binary64` -> `binary32`) it is sometimes important to know if the conversion is performed *with no loss of precision*. I was unable to find an easy way to perform such a check, and thus this project was born.

## Key features
* Decidable precise equality on floats with no dependency on `R` ([FloatPair.v](FloatPair.v))
* Value-preserving operations to shift a float "up"/"down" in a cohort ([Cohorts.v](Cohorts.v))
* Converting an arbitrary float into an IEEE-754-normalized form without loss of precision ([normalize_pair](https://github.com/zoickx/float-cohorts/blob/86e72969a62cccc6226707c065dc0ab938115d72/Normalization.v#L104))
* Natural normalization of arbitrary floats ([maximize_e](https://github.com/zoickx/float-cohorts/blob/86e72969a62cccc6226707c065dc0ab938115d72/Normalization.v#L15))

## Building
Install prerequisites:
``` shell
opam install coq
```

Clone and build:
``` shell
git clone https://github.com/zoickx/float-cohorts 
cd float-cohorts
make
```
