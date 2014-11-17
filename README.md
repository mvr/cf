CF
==

This package provides an implementation of Gosper's algorithm for performing arithmetic on (possibly infinite) continued fractions. This allows us to do arbitrary precision real arithmetic without deciding in advance how much precision we need.

The type `CF` currently has instances for the following typeclasses.
* `Eq`
* `Ord`
* `Num`
* `Enum`
* `Fractional`
* `Real`
* `RealFrac`

Implementing the trancendental functions in `Floating` will require switching to a cleverer representation for `CF`

Examples
--------

The following calculates `e + sqrt(2)` to high precision:

```haskell
λ> take 200 $ showCF (exp1 + sqrt2)
4.132495390832140284161976195562360576326918969076907648143647365714809108815654633421769712852808000162480238162915356946742249652479780785544455792360531462151354994555449083519033780381905977311590
```
