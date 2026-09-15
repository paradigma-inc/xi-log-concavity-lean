# Shared rounded power states across the grid

Store each certified root pair together with its current outward-rounded integer power pair. The lower update is $L\mapsto\lfloor L\ell/B\rfloor$; the upper update is $U\mapsto-\lfloor-Uu/B\rfloor$. These are exactly the already accepted rounded-power recurrences, not new enclosures.

Starting at exponent $n$, advancing by $k$ steps gives precisely the old evaluator's endpoints at exponent $n+k$. The proof is induction on $k$, first for one state and then for a whole mapped root table; table length is preserved. Starting at exponent 40 gives the actual positive-base power $a^{-(k+40)/80}$ with the same rational root conditions as before.

The signed weighted lower/upper terms computed from these states are definitionally equal to the accepted integer eta terms. Thus a future block checker can reuse the previous grid state instead of recomputing every power from exponent zero.

No precision, directed rounding, coefficient, analytic remainder or endpoint changes. This module proves arithmetic reuse and actual enclosure preservation; it does not certify any additional retained source sample.
