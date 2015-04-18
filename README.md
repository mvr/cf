CF
==

This package implements Gosper's algorithm for arithmetic on (often
infinite) continued fractions. This allows us to do arbitrary
precision calculations without deciding in advance how much precision
we need. Following Vuillemin, our continued fractions may contain zero
and negative terms, so that the functions in `Floating` can be
supported.

The type `CF` has instances for the following typeclasses.
* `Eq`
* `Ord`
* `Num`
* `Fractional`
* `RealFrac`
* `Floating` (currently missing `pi`, `asin`, `acos`, `atan`)

Because equality of real numbers is not computable, we consider two
numbers `==` if they are closer than `epsilon = 1 % 10^10`. For the
same reason, `floor` and its cousins may give an incorrect result when
the argument is within `epsilon` of an integer.

References
----------

* Gosper, Ralph W. "Continued fraction arithmetic." HAKMEM Item 101B, MIT Artificial Intelligence Memo 239 (1972). APA
* Vuillemin, Jean E. "Exact real computer arithmetic with continued fractions." Computers, IEEE Transactions on 39.8 (1990): 1087-1105.
* Lester, David R. "Vuillemin’s exact real arithmetic." Functional Programming, Glasgow 1991. Springer London, 1992. 225-238. APA
