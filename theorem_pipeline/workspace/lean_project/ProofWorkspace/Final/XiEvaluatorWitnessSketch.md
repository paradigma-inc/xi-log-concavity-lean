# A finite witness for the complete Xi evaluator

The unconditional theorem `xi_two_rational_evaluator_witness` proves
$1/4 < \operatorname{Re}\xi(2) < 1$ using the assembled rational evaluator.
It takes no enclosure assumptions.

The grid index is $k=120$, so $(k+40)/80=2$. The fixed evaluation parameters
are four eta terms, four Gamma-series terms, eight integer-zeta terms,
three logarithm terms, scale four and eight exponential terms.
`xiTwoWitnessChecks` verifies every explicit rational range and denominator
condition. `xiTwoWitnessEndpoints` proves the rational endpoint inequalities
with kernel-checked arithmetic. The actual-Xi enclosure theorem then transfers
those inequalities to the analytic function.

The interval is deliberately coarse. Its role is to demonstrate a complete
finite proof through the evaluator, not to certify the retained high-precision
node table or advance the global curvature claim by itself. No runtime Boolean
check, extra axiom or assumed numerical accuracy is used.
