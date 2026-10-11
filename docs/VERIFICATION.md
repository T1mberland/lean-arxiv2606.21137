# Verification results

Verified locally on 11 October 2026 with Lean 4.34.1 and the pinned dependencies
in `lake-manifest.json`.

| Check | Result |
|---|---|
| `MATHLIB_NO_CACHE_ON_UPDATE=1 lake update` | Exit 0; toolchain already current; root and Mathlib post-update hooks ran |
| Compatibility bootstrap from pristine Sudakov source | Passed; update hook reproduced the exact expected patched-source SHA-256 |
| Repeated dependency update | Exit 0; compatibility hook is idempotent |
| `lake build` | **Exit 0**, `Build completed successfully (3475 jobs).` |
| `lake env lean examples/Import.lean` | **Exit 0**, 20 independent examples importing the complete public library, including Theorem 7.2, its empty-family case, both spectral-edge estimates, concentration, and the asymptotic limsup |
| `lake env lean docs/Statements.lean` | **Exit 0**, 277 exported theorem type checks; output in [statements.txt](statements.txt) |
| `lake env lean scripts/Audit.lean` | **Exit 0**, recursive audit of **494** project declarations; output in [axiom-audit.txt](axiom-audit.txt) |
| Mathematical source scan | All 37 mathematical source files contain no proof placeholders, custom axiom, opaque, or constant declarations |
| Git whitespace check | Passed |

The build summary was:

```text
✔ [3473/3475] Built LehnerEdges.Asymptotics (5.3s)
✔ [3474/3475] Built LehnerEdges (2.7s)
Build completed successfully (3475 jobs).
```

The build emits upstream deprecation/style warnings and local tactic-style
and unused-variable warnings. It emits no proof-placeholder warnings or errors. Mathlib and some
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
PASS: recursively audited 494 project declarations; only propext, Classical.choice, Quot.sound permitted.
```

The same file also runs explicit `#print axioms` commands on the assembled
comparison, variational, concentration, trace-duality, spectral, and block
bounds, as well as the external Sudakov–Fernique and Gaussian concentration
theorems used here. Every printed list consists of exactly the three standard
foundational axioms above. The full captured output is
[axiom-audit.txt](axiom-audit.txt).

This audit includes **Theorem 7.2**, the stronger constant-eight norm bound,
both expected spectral-edge bounds, the joint Hermitian-test GUE laws,
Gaussian concentration for the actual matrix norm, and Corollary 1.2's
finite-variational asymptotic conclusions. In particular:

```text
'LehnerEdges.theorem_7_2' depends on axioms: [propext, Classical.choice, Quot.sound]
'LehnerEdges.expected_norm_limsup_le_of_edge_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound]
```

It does not certify the free-edge identification or the other unformalized
results listed in [FORMALIZATION.md](FORMALIZATION.md).
