/-
Copyright (c) 2026 Tyler B. Hughes. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Data.Rat.Defs
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Palomar Challenge: Universal `81 / 29` Bound for Tuza's Triangle-Cover Conjecture

For every finite simple graph `G`, let `ν(G)` be the maximum number of
pairwise edge-disjoint triangles in `G` and `τ(G)` be the minimum number of
edges meeting every triangle in `G`.

This challenge states the unconditional bound

  `29 * τ(G) ≤ 81 * ν(G)`   (`τ(G) ≤ (81 / 29) * ν(G) ≈ 2.793103 * ν(G)`),

strictly improving Sichen Wang's `165 / 59` bound (`arXiv:2609.13831`),
together with an explicit transversal witness form and non-vacuity checks on
the complete graph `K_4` (`ν(K_4) = 1`, `τ(K_4) = 2`).

All definitions here use only Mathlib primitives (`SimpleGraph`, `Sym2`,
`Finset`, `sSup`, `sInf`).
-/

@[expose] public section

namespace TuzaChallenge

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The three unoriented edges on vertices `u, v, w`. -/
def triangleEdges (u v w : V) : Finset (Sym2 V) :=
  {s(u, v), s(u, w), s(v, w)}

/-- An edge set is a triangle when it consists of the three edges on three distinct vertices. -/
def IsTriangle (T : Finset (Sym2 V)) : Prop :=
  ∃ u v w, u ≠ v ∧ u ≠ w ∧ v ≠ w ∧ T = triangleEdges u v w

/-- All triangles whose edges lie in `A`. -/
noncomputable def trianglesOn (A : Finset (Sym2 V)) : Finset (Finset (Sym2 V)) := by
  classical
  exact univ.filter (fun T => IsTriangle T ∧ T ⊆ A)

/-- The edge set of a finite simple graph as a `Finset`. -/
noncomputable def graphEdges (G : SimpleGraph V) : Finset (Sym2 V) := by
  classical
  exact G.edgeSet.toFinset

/-- All triangles of a finite simple graph `G`. -/
noncomputable def graphTriangles (G : SimpleGraph V) : Finset (Finset (Sym2 V)) :=
  trianglesOn (graphEdges G)

/-- A triangle packing is a subset of `F` whose members are pairwise edge-disjoint. -/
def IsPacking (F P : Finset (Finset (Sym2 V))) : Prop :=
  P ⊆ F ∧ (P : Set (Finset (Sym2 V))).Pairwise Disjoint

/-- A triangle cover (transversal) meets every triangle in `F` in at least one edge. -/
def IsCover (F : Finset (Finset (Sym2 V))) (C : Finset (Sym2 V)) : Prop :=
  ∀ T ∈ F, (T ∩ C).Nonempty

/-- Maximum number of pairwise edge-disjoint triangles in `G`. -/
noncomputable def nu (G : SimpleGraph V) : ℕ :=
  sSup {n : ℕ | ∃ P : Finset (Finset (Sym2 V)), IsPacking (graphTriangles G) P ∧ P.card = n}

/-- Minimum number of edges meeting every triangle in `G`. -/
noncomputable def tau (G : SimpleGraph V) : ℕ :=
  sInf {n : ℕ | ∃ C : Finset (Sym2 V), IsCover (graphTriangles G) C ∧ C.card = n}

/-- **Main Theorem (Natural-Number Form):** Every finite simple graph `G`
satisfies `29 * τ(G) ≤ 81 * ν(G)`. -/
theorem tuza_bound_81_29_nat (G : SimpleGraph V) :
    29 * tau G ≤ 81 * nu G := by
  sorry

/-- **Main Theorem (Rational Form):** Every finite simple graph `G`
satisfies `τ(G) ≤ (81 / 29) * ν(G)`. -/
theorem tuza_bound_81_29 (G : SimpleGraph V) :
    (tau G : ℚ) ≤ (81 / 29 : ℚ) * nu G := by
  sorry

/-- **Explicit Transversal Witness:** Every finite simple graph `G` has an edge
subset `C ⊆ E(G)` hitting every triangle of `G` with `29 * |C| ≤ 81 * ν(G)`. -/
theorem exists_small_triangle_transversal_81_29 (G : SimpleGraph V) :
    ∃ C : Finset (Sym2 V), C ⊆ graphEdges G ∧
      (∀ u v w, G.Adj u v → G.Adj u w → G.Adj v w →
        s(u, v) ∈ C ∨ s(u, w) ∈ C ∨ s(v, w) ∈ C) ∧
      29 * C.card ≤ 81 * nu G := by
  sorry

/-- **Non-Vacuity (`ν(K_4) = 1`)** -/
theorem nu_complete4 : nu (⊤ : SimpleGraph (Fin 4)) = 1 := by
  sorry

/-- **Non-Vacuity (`τ(K_4) = 2`)** -/
theorem tau_complete4 : tau (⊤ : SimpleGraph (Fin 4)) = 2 := by
  sorry

end TuzaChallenge
