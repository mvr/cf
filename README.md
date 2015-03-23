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

Notes
-----

TODO:
- Rational results
- Computability of Eq, Ord and RealFrac

References
----------

* Gosper, Ralph W. "Continued fraction arithmetic." HAKMEM Item 101B, MIT Artificial Intelligence Memo 239 (1972). APA
* Vuillemin, Jean E. "Exact real computer arithmetic with continued fractions." Computers, IEEE Transactions on 39.8 (1990): 1087-1105.
* Lester, David R. "Vuillemin’s exact real arithmetic." Functional Programming, Glasgow 1991. Springer London, 1992. 225-238. APA
