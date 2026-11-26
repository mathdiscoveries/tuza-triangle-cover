# Universal `81 / 29` Bound for Tuza's Triangle-Cover Conjecture

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24490771.svg)](https://doi.org/10.5281/zenodo.24490771)

Unconditional Lean 4 (`v4.35.0`) + Mathlib formalization proving

$$29\,\tau(G) \le 81\,\nu(G) \qquad \left(\tau(G) \le \frac{81}{29}\,\nu(G) \approx 2.793103\,\nu(G)\right)$$

for every finite simple graph $G$, where $\nu(G)$ is the maximum number of
pairwise edge-disjoint triangles in $G$ and $\tau(G)$ is the minimum number of
edges meeting every triangle in $G$.

The Lean code extends Sichen Wang's MIT-licensed
[`sichen-wang/tuza-lean`](https://github.com/sichen-wang/tuza-lean)
($\frac{165}{59}\nu(G)$, `arXiv:2609.13831`) and formalizes the
helper-arborescence coupling, unmerged colored-family covers, and opposite-edge
elimination of the companion paper,
[An 81/29 Upper Bound for Tuza's Conjecture via Helper Arborescences and Opposite-Edge Elimination](https://mathdiscoveries.org/results/tuza-triangle-cover).

## Compared Theorems (`Challenge.lean` / `comparator.json`)

- `TuzaChallenge.tuza_bound_81_29_nat`: `29 * tau G ≤ 81 * nu G`
- `TuzaChallenge.tuza_bound_81_29`: `(tau G : ℚ) ≤ (81 / 29 : ℚ) * nu G`
- `TuzaChallenge.exists_small_triangle_transversal_81_29`: explicit edge subset `C ⊆ E(G)` hitting every triangle with `29 * |C| ≤ 81 * nu G`
- `TuzaChallenge.nu_complete4`: `nu (⊤ : SimpleGraph (Fin 4)) = 1`
- `TuzaChallenge.tau_complete4`: `tau (⊤ : SimpleGraph (Fin 4)) = 2`

All proofs use only Lean's three standard axioms (`propext`, `Quot.sound`,
`Classical.choice`), with zero `sorry` and zero `native_decide`.

## Build & Verify

```bash
lake build Challenge Solution TuzaBound
lake env lean TuzaBound/Verify.lean
lake comparator --paranoid --inadvisably-no-sandbox
```
