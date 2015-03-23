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
* `Floating` (In progress)

References
----------

* Vuillemin, Jean E. "Exact real computer arithmetic with continued fractions." Computers, IEEE Transactions on 39.8 (1990): 1087-1105.
