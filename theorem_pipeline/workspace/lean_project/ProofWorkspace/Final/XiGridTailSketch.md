# Certified Fourier-grid tail without Stirling

Exact rational exponential Taylor bounds prove
$\log84\ge4.43$, $\log\pi\le1.146$, and
$e^{9.57}\le115599/8$. These are checked by Lean's kernel, not supplied
by a floating-point evaluator.

For $u\ge340$, put $s=(1+u)/2\ge170.5$. The actual Euler Gamma integral,
restricted to $[84,85]$, gives

$$\Gamma(s/2)\ge e^{-85}84^{s/2-1}.$$

The actual zeta series is at least one. Retaining the polynomial factor
in Xi, rather than discarding it, therefore yields

$$\xi(s)\ge\frac{s(s-1)}2\pi^{-s/2}e^{-85}84^{s/2-1}.$$

The polynomial factor is at least $115599/8\ge e^{9.57}$.
The directed logarithm bounds then show that the logarithm of this lower
bound is at least $200+(4/5)(u-340)$. Hence

$$\xi((1+u)/2)\ge e^{200+(4/5)(u-340)}.$$

The earlier central theta estimate bounds $|\xi(1/2)|\le1$.
Dividing, using the proved nonzero denominator and evenness, proves

$$|\varphi(u)|\le e^{-200}e^{-(4/5)(|u|-340)}
\qquad(|u|\ge340).$$

The result applies to every point of the tail, not just its initial grid
sample. It can therefore control the omitted Fourier sum. It does not
certify the retained Xi samples or the recorded polynomial coefficients.
