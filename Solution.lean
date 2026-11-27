/-
Copyright (c) 2026 Tyler B. Hughes. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Data.Rat.Defs
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import TuzaBound

/-!
# Palomar Solution: Universal `81 / 29` Bound for Tuza's Triangle-Cover Conjecture

Bridges the pure-Mathlib `sSup`/`sInf` definitions in `TuzaChallenge` to the
full `TuzaBound` proof library.
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

private theorem nu_eq_tuzaBound (G : SimpleGraph V) : nu G = TuzaBound.nu G := by
  unfold nu
  let S : Set ℕ :=
    {n : ℕ | ∃ P : Finset (Finset (Sym2 V)), IsPacking (graphTriangles G) P ∧ P.card = n}
  have hmem : TuzaBound.nu G ∈ S := by
    obtain ⟨P, hP, hcard⟩ := (TuzaBound.le_nu_iff G (TuzaBound.nu G)).mp (le_refl _)
    have hle : P.card ≤ TuzaBound.nu G := hP.card_le
    exact ⟨P, hP, Nat.le_antisymm hle hcard⟩
  have hbdd : BddAbove S := by
    refine ⟨TuzaBound.nu G, ?_⟩
    rintro n ⟨P, hP, rfl⟩
    exact TuzaBound.IsPacking.card_le hP
  exact Nat.le_antisymm (csSup_le ⟨TuzaBound.nu G, hmem⟩ (by
    rintro n ⟨P, hP, rfl⟩
    exact TuzaBound.IsPacking.card_le hP)) (le_csSup hbdd hmem)

private theorem tau_eq_tuzaBound (G : SimpleGraph V) : tau G = TuzaBound.tau G := rfl

theorem tuza_bound_81_29_nat (G : SimpleGraph V) :
    29 * tau G ≤ 81 * nu G := by
  rw [tau_eq_tuzaBound, nu_eq_tuzaBound]
  exact TuzaBound.tuza_bound_81_29_nat G

theorem tuza_bound_81_29 (G : SimpleGraph V) :
    (tau G : ℚ) ≤ (81 / 29 : ℚ) * nu G := by
  rw [tau_eq_tuzaBound, nu_eq_tuzaBound]
  exact TuzaBound.tuza_bound_81_29 G

theorem exists_small_triangle_transversal_81_29 (G : SimpleGraph V) :
    ∃ C : Finset (Sym2 V), C ⊆ graphEdges G ∧
      (∀ u v w, G.Adj u v → G.Adj u w → G.Adj v w →
        s(u, v) ∈ C ∨ s(u, w) ∈ C ∨ s(v, w) ∈ C) ∧
      29 * C.card ≤ 81 * nu G := by
  rw [nu_eq_tuzaBound]
  exact TuzaBound.exists_small_triangle_transversal_81_29 G

theorem nu_complete4 : nu (⊤ : SimpleGraph (Fin 4)) = 1 := by
  rw [nu_eq_tuzaBound]
  exact TuzaBound.nu_complete4

theorem tau_complete4 : tau (⊤ : SimpleGraph (Fin 4)) = 2 := by
  rw [tau_eq_tuzaBound]
  exact TuzaBound.tau_complete4

end TuzaChallenge
