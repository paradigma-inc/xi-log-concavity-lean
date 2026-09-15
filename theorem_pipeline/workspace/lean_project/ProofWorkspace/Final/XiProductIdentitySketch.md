# Actual Xi paired-product identity

## Statement

For the actual normalized entire function $F(z)=\xi(1/2+iz/2)/4$,
$$F(w)=F(0)\prod_{\operatorname{Re}a>0}\left(1-\frac{w^2}{a^2}\right),$$
where the product is over all actual zeros, repeated with their proved finite analytic multiplicities.

## Assumptions

None beyond the definitions of the actual functions. In particular there is no RH assumption, supplied complete zero list, assumed product identity, or assumed zero-free-factor constancy.

## Proof Sketch

The preceding actual-function proofs establish Jensen counting, inverse-square summability, compact-uniform product convergence, equality of zero multiplicities, and an entire nonvanishing quotient. Its normalized entire logarithm has zero value and derivative at zero. Actual Xi growth, paired-product growth, and the first main theorem show that the positive-real-part circle average of this logarithm is subquadratic. The separately proved entire-function rigidity theorem makes it zero identically. Substitution into the exact exponential factorization yields the claimed product identity.

This closes the product identity only. Finite low-zero certification, the positive residual measure, the remaining numerical panels, and the final global density theorem are not consequences claimed by this module.

## Lean Artifacts

- File: `XiProductIdentityFull.lean`
- Main theorems: `F_eq_pairedProduct`, `F_div_zero_eq_pairedProduct`.
