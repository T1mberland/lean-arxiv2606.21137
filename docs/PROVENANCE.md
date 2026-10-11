# Sources, dependencies, and attribution

## Paper

Benoît Collins and Yuta Yamagishi, *A Sudakov–Fernique proof of Lehner-type edge
bounds for matrix-valued GUE sums*, arXiv:2606.21137**v2**.

- Versioned abstract: https://arxiv.org/abs/2606.21137v2
- Versioned PDF: https://arxiv.org/pdf/2606.21137v2
- PDF header: arXiv v2 dated 7 August 2026; manuscript title page dated
  10 August 2026. The downloaded PDF has 22 pages.
- Source reviewed in full, including Sections 1–9, proofs, and references,
  before implementing the matrix lemmas.

The downloaded PDF SHA-256 is
`b68b67e3e8fbd447c9ae6f068b9cef07b2491c7571454c436b1f69b6c0453689`.

The source PDF is not redistributed in this repository. The mathematical
statements and proof structure are attributed to the paper. In particular,
the Stiefel increment lemma is proved here through elementary positive traces,
rather than by importing an unformalized general square-root inequality.

## Reused Lean results

| Dependency | Pinned revision | Use |
|---|---|---|
| Mathlib | `v4.34.1`, commit `d13f23b723b8a846827a245b89c10fc7d3f11612` | Matrix operator norm and order, continuous functional calculus, matrix inverse, spectral calculus, finite-dimensional Gaussian measures, integration, subgaussian MGF and tail API |
| [T1mberland/Lean-Sudakov](https://github.com/T1mberland/Lean-Sudakov) | `bcd86db77e0153159977b8085f7ffdd993a3d3e9` | `sudakov_fernique_drift`, `vecMax`, `gaussian_integrable_vecMax_drift` in `LeanSudakov.SudakovFerniqueDrift` and its imports |
| [T1mberland/lean-log-sobolev](https://github.com/T1mberland/lean-log-sobolev) | `1a95157e7d4cc18d444aa640c751acbe4c7692d4` | `LogSobolev.gaussian_integrable_of_lipschitz` and `LogSobolev.gaussian_hasSubgaussianMGF` in `LogSobolev.Concentration.Gaussian` |

Mathlib is Apache 2.0. lean-log-sobolev is Apache 2.0 and retains the copyright
and attribution notices of its Gaussian logarithmic Sobolev ports. These
notices remain in the dependency sources. No theorem source from either
suggested repository has been copied into this project's mathematical files.
The pinned Lean-Sudakov repository has no top-level LICENSE file; this project
does not purport to relicense its sources.

The exact dependency graph, including transitive packages, is recorded in
`lake-manifest.json`. Local precompiled caches were reused to avoid rebuilding
Mathlib; they are not required by the manifest or committed to Git.

## Compatibility change

Both suggested repositories target Lean 4.34.1 at these revisions, so no
mathematical port across Lean versions was needed. Importing them together
nevertheless exposes a duplicate global declaration `map_update_prod_pi`.
The root `lakefile.lean` update hook replaces this identifier, at its declaration
and its one use in Lean-Sudakov's `GaussianVectorIBP.lean`, with
`LehnerSudakovCompat.map_update_prod_pi`. The statement and proof are byte-for-byte
unchanged apart from that identifier. The change is applied idempotently after
`lake update` and is required to combine comparison and concentration in one
Lean environment.

## Proof audit

The external results are not treated as trusted custom axioms. The project
audit recursively inspects every dependency of every declaration originating
in a `LehnerEdges` module, including the imported comparison and logarithmic
Sobolev proofs. Its only allowed axioms are `propext`, `Classical.choice`, and
`Quot.sound`.
