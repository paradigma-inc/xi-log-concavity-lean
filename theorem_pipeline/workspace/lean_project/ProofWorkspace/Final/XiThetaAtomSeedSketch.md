# Actual theta atom seed errors

## Statement

The actual atom $c^{-3/4+12i}e^{-\pi k^2c}$ is identified with a complex exponential. Approximating $\log c$ within $e$ and $\pi$ within $d$ perturbs its exponent by at most $13e+k^2cd$. The scaled Taylor/squaring certificate transfers to the actual atom with this input error included.

## Assumptions

$c\ge1$ for the nonpositive-real-part and seed certificate, the stated logarithm and pi errors, and the explicit finite seed, norm, and rounded-squaring checks. The total input error is at most one. No numerical input is assumed implicitly.

## Proof Sketch

The principal complex power agrees with the exponential of the real logarithm at positive inputs. The exponent multiplier has norm at most thirteen. Triangle and product inequalities give the exponent perturbation bound; the previously proved complex exponential error theorem then includes the input perturbation and every rounding step.

## Lean Artifacts

`XiThetaAtomSeedFull.lean`: complexPowerExpAtom_real_eq_exp, complexThetaExponent48_norm_le, theta48AtomExponent_nonpos, theta48AtomExponent_approx_error, theta48Atom_seed_certificate.
