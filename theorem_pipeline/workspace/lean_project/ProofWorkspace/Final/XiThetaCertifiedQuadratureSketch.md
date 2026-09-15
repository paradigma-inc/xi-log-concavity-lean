# Certified real-axis value at 48

## Statement

The actual analytic function satisfies
$$5.29169286414\times10^{-7}<F(48)<5.29196177592\times10^{-7}.$$
These are the original source endpoints, not a fitted replacement interval.

## Assumptions

There are no numerical hypotheses. The proof depends on all 32 concrete panel
certificates and the previously proved analytic truncation and integration
estimates, including the original certified pi and logarithm inputs.

## Proof Sketch

Each rational panel value is within $320\times10^{-25}$ of its exact forty-term
Taylor panel integral. Summing all panels and adding the proved analytic Taylor
and integral truncation errors gives an error at most $3\times10^{-16}$ after
the exact normalization defining $F(48)$. Lean evaluates the sum of certified
rational values and checks that this entire error interval lies strictly inside
the source interval. The generator only proposes the rational sum; Lean checks
the equality and the endpoint comparisons.

## Lean Artifacts

- `XiThetaCertifiedQuadratureFull.lean`
- `F48_source_enclosure`, `F48_source_lower`

This numerical theorem does not certify finite zero completeness or the global
strict log-concavity conclusion by itself.
