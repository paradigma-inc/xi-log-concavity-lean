# Root-power grid certificate

## Statement

For every integer $1 \\le a \\le 400$, the certificate stores rational endpoints
$l_a,u_a$ on the grid $10^{-180}\\mathbb Z$ and proves
$0\\le l_a$, $a l_a^{80}\\le 1$, and $1\\le a u_a^{80}$.

## Assumptions

The certificate consists of the complete ordered rows $a=1,\\ldots,400$.
The denominator is $B=10^{180}$, and each endpoint is an integer numerator
divided by $B$.

## Proof Sketch

The rows are generated as exact integer data and checked by the kernel through
the scaled inequalities $aL_a^{80}\\le B^{80}\\le aU_a^{80}$.
The list length and its base projection are proved by computation, so the
indexed accessor for each $a$ is shown to select the row with base $a$.
Clearing the positive denominator $B^{80}$ gives the rational inequalities
for $l_a=L_a/B$ and $u_a=U_a/B$. The imported
rational_root80_enclosure theorem can then convert these polynomial checks
into an enclosure for the actual value $a^{-1/80}$; this certificate does not
claim any retained Xi source-node certification.

## Lean Artifacts

- File: ProofWorkspace/Final/RootPowerCertificateFull.lean
- Theorems:
  - rootCertificateRows_length
  - rootCertificateRows_cover
  - rootCertificateChecks
  - rootCertificateRows_rational_checks
  - rootCertificate_index_base
  - rootPowerGridBounds

