# Packaging and validation

This standalone distribution was prepared on 15 September 2026 from the
completed proof-and-audit archive dated 11 September 2026.

Original archive SHA-256:
`9aa96c13e29765840bdeaf5f3ff56db4383d0fbde907de927b62524098c29f88`.

All **4,625 included Lean source files** are byte-identical to both that archive
and the completed local proof workspace. No theorem statement, proof body,
numerical constant, module name, or toolchain pin was changed in packaging.
The original final independent audit is preserved unchanged. The later
literature addendum and the updated verification report are also included.

The repository retains the original relative layout so source and audit links
continue to resolve. Some historical verification records refer to earlier
per-panel logs or cluster manifests retained in the original workspace; this
distribution contains the full formal library and the selected final records,
not every interrupted attempt or historical execution log.

The root README is the entry point for this repository. `SHARING_README.md` is
the historical distribution index from the original archive.

## Fresh check on 15 September 2026

The final six-declaration axiom inspection was rerun successfully in 76.07
seconds. Each declaration depends only on `propext`, `Classical.choice`, and
`Quot.sound`. See the [raw output](validation/axioms-20260915.log) and
[run summary](validation/axioms-20260915.json).

This check used the original verified compiled dependencies and the distributed
audit source. It was not a clean rebuild of all numerical proofs. The source
comparison verified that every distributed Lean file is byte-identical to the
completed project, and all local imports resolve within the included library.

To verify all distributed Lean source checksums from the repository root:

```sh
shasum -a 256 -c LEAN_SOURCES.sha256
```
