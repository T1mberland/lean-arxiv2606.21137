# Verification results

Verified locally on 11 October 2026 with Lean 4.34.1 and the pinned dependencies
in `lake-manifest.json`.

| Check | Result |
|---|---|
| `MATHLIB_NO_CACHE_ON_UPDATE=1 lake update` | Exit 0; toolchain already current; root and Mathlib post-update hooks ran |
| Compatibility bootstrap from pristine Sudakov source | Passed; update hook reproduced the exact expected patched-source SHA-256 |
| Repeated dependency update | Exit 0; compatibility hook is idempotent |
| `lake build` | **Exit 0**, `Build completed successfully (3453 jobs).` |
| `lake env lean examples/Import.lean` | **Exit 0**, seven independent examples importing the complete public library |
| `lake env lean docs/Statements.lean` | **Exit 0**, 109 exported theorem type checks; output in [statements.txt](statements.txt) |
| `lake env lean scripts/Audit.lean` | **Exit 0**, recursive audit of **195** project declarations; output in [axiom-audit.txt](axiom-audit.txt) |
| Mathematical source scan | All 16 mathematical source files contain no proof placeholders, custom axiom declarations, or opaque declarations |
| Git whitespace check | Passed |

The build summary was:

```text
✔ [3450/3453] Built LehnerEdges.GaussianMatrices (29s)
✔ [3451/3453] Built LehnerEdges.Wishart (7.7s)
✔ [3452/3453] Built LehnerEdges (2.8s)
Build completed successfully (3453 jobs).
```

The build emits upstream deprecation/style warnings and one local tactic-style
warning. It emits no proof-placeholder warnings or errors. Mathlib and some
external precompiled dependency artifacts were reused; this was not a rebuild
of every external dependency from an empty cache. All project modules were
compiled, and importing both external libraries in the same environment was
verified.

## Axiom audit

[scripts/Audit.lean](../scripts/Audit.lean) selects every declaration originating
in a module whose name starts with `LehnerEdges`, including helper definitions
and generated declarations. For each it calls `Lean.collectAxioms`, following
both type and proof dependencies transitively. It fails if no declarations
are selected or if any axiom is outside this exact allowlist:

```text
propext
Classical.choice
Quot.sound
```

The successful result was:

```text
PASS: recursively audited 195 project declarations; only propext, Classical.choice, Quot.sound permitted.
```

The same file also runs explicit `#print axioms` commands on the assembled
comparison, variational, concentration, trace-duality, spectral, and block
bounds, as well as the external Sudakov–Fernique and Gaussian concentration
theorems used here. Every printed list consists of exactly the three standard
foundational axioms above. The full captured output is
[axiom-audit.txt](axiom-audit.txt).

This audit applies to the completed partial development. It does **not**
certify Theorem 7.2, the expected spectral-edge estimates, or the free-edge
identification: those are absent from the proved API, as detailed in
[FORMALIZATION.md](FORMALIZATION.md).
