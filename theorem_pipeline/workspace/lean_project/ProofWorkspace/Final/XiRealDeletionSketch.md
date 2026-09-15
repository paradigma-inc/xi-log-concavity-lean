# Deleting real zero occurrences

## Statement and assumptions

Complex conjugation fixes every actual positive zero occurrence whose root is real, including its multiplicity index. Removing any finite collection of such occurrences therefore leaves a conjugation-invariant complement. In particular this applies to two occurrences with roots $a,b\in\mathbb R$.

## Proof Sketch

Conjugation fixes the root and preserves its analytic multiplicity; the indexed occurrence itself is thus fixed. If the conjugate of a remaining occurrence belonged to the deleted set, applying the involution would put the original occurrence there too. The two-root case follows by finite membership elimination.

No existence, location, or simplicity of any real root is asserted here.

## Lean artifacts

- `XiRealDeletionFull.lean`
- `F_pairConj_eq_self_of_real`
- `F_pairConj_compl_finite_real`
- `F_pairConj_compl_two_real`
