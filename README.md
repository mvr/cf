CF
==

This package implements Gosper's algorithm for arithmetic on (possibly infinite) continued fractions. This allows us to do arbitrary precision calculations without deciding in advance how much precision we need.

The type `CF` has instances for the following typeclasses.
* `Eq`
* `Ord`
* `Num`
* `Enum`
* `Fractional`
* `Real`
* `RealFrac`

Implementing the transcendental functions in `Floating` will require switching to a better representation for `CF`.

Examples
--------

The following calculates `e + sqrt(2)` to high precision, using the provided continued fraction representations of `e` and `sqrt(2)`:

```haskell
λ> take 200 $ showCF (exp1 + sqrt2)
4.132495390832140284161976195562360576326918969076907648143647365714809108815654633421769712852808000162480238162915356946742249652479780785544455792360531462151354994555449083519033780381905977311590
```
