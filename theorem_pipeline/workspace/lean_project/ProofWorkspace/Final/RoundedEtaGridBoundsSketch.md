# Rounded eta sums using grid power reuse

At $s_k=(k+40)/80>0$, each Euler summand is a signed rational coefficient
times $(j+1)^{-s_k}$. The proved geometric grid evaluator encloses that power;
min/max multiplication handles the coefficient sign, and each term is rounded
outward to the integer scale $B$ before summation.

The finite lower sum remains below the actual eta integral. The finite upper
sum receives the proved one-sided analytic remainder $2^{-N}$. A final outward
round returns both endpoints to the fixed grid. These steps prove
`ratEtaGridRounded_enclosure`, with $m,n,B>0$ and explicit rational initialization
checks for each of the $N$ natural bases. Those checks are independent of $k$.

`ratEtaGridRounded_mem_grid` verifies integer-scaled output endpoints. Neither
the analytic eta error nor rounding error is discarded, and no supplied
real-valued sample or assumed numerical accuracy enters the theorem.
