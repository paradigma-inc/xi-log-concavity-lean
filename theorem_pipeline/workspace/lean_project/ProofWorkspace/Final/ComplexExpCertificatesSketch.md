# Checked complex exponential evaluation bounds

## Statement

The forty-term exponential Taylor polynomial has error at most $10^{-47}$ on the unit disk. For nonpositive real-part inputs, ten rounded squarings after scaling by 1024 give total error
$$1024(\eta+10^{-47})+1023\rho+2\varepsilon,$$
where $\eta$ is the seed rounding error, $\rho$ bounds each squaring error, and $\varepsilon\le1$ bounds input error.

## Assumptions

The scaled approximate input is in the unit disk. Both input real parts are nonpositive. The stated seed and squaring errors hold, and every stored pre-squaring state has norm at most one. These finite checks must be discharged for each numerical seed.

## Proof Sketch

Apply the complex exponential Taylor remainder theorem and evaluate its factorial bound exactly. Factor an exponential difference to control input perturbations. A difference of squares between unit-ball elements has norm at most twice their distance. Induction through the ten squarings gives the geometric accumulation formula, and the exact exponential multiplication identity identifies the final target.

## Lean Artifacts

- Full proof: `ComplexExpCertificatesFull.lean`
- Theorems: `complexExpTaylor40_error`, `complexExp_input_error`, `complex_square_error`, `complex_rounded_squaring_error`, `complexExp_scaled1024_certificate`.
