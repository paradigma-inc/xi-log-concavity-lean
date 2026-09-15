# Error propagation for a complex two-step recurrence

## Statement

A rounded complex recurrence with bounded transition residuals approximates an exact second-order recurrence within any explicitly certified error-radius sequence. The one-step estimate includes both previous errors and the new residual.

## Assumptions

The exact recurrence, initial errors, coefficient norm bounds, transition residual bounds, and error-radius inequalities are explicit hypotheses. This generic theorem alone certifies no theta coefficient.

## Proof Sketch

Factor the difference of each pair of linear terms, then use norm subadditivity and multiplicativity. Strong induction applies the resulting one-step estimate to the two preceding errors. An additional linear-pair lemma accounts for perturbations of both transition coefficients.

## Lean Artifacts

`ComplexRecurrenceErrorFull.lean`: complex_linear_pair_perturbation, complex_recurrence_step_error, complex_second_order_error.
