/-
Copyright (c) 2026 Sichen Wang. All rights reserved.
Released under MIT license as described in the file LICENSE.
Adapted and extended from https://github.com/sichen-wang/tuza-lean (Lean v4.32.0 -> v4.35.0, namespace TuzaBound).
-/
module

public import TuzaBound.Construction.FirstCover
public import TuzaBound.Construction.BookCover
public import TuzaBound.Construction.ColoredCover
public import TuzaBound.Construction.HelperArborescence
public import TuzaBound.Construction.OppositeElimination
public import TuzaBound.Basic.Graph

/-!
# Main Theorems: `29 * τ(G) ≤ 81 * ν(G)` (`τ(G) ≤ (81 / 29) * ν(G)`) and `250 * τ(G) ≤ 699 * ν(G)`

1. **Main Theorem (`29 * tau G ≤ 81 * nu G`, `(81 / 29) * ν(G) ≈ 2.793103 * ν(G)`)**:
   Combines the six simultaneous transversal inequalities `(3)`, unrelaxed `(4'')`, `(5)`,
   opposite-elimination `(5'')`, and elementary non-recursive `(6a)` and `(6b)`
   with integer weights `(10, 4, 8, 1, 2, 4)` (`(10, 1, 8, 1, 2, 4)` after clearing `4 *` in
   `(4'')`) to prove `29 * tau G ≤ 81 * nu G` unconditionally for every finite simple graph
   `G : SimpleGraph V`.
2. **Intermediate Bound (`250 * tau G ≤ 699 * nu G`, `2.796 * ν(G)`) & Wang Corollary (`165 / 59`)**:
   Retains the full explicit 5-inequality proof `(3) + (4') + (5) + (6a) + (6c)` (`tuza_bound_nat`,
   `tuza_bound`, `exists_small_triangle_transversal`), derives it as a 1-line corollary of `81 / 29`
   (`bound_699_250_from_81_29`), recovers Sichen Wang's `59 * tau G ≤ 165 * nu G`
   (`wang_bound_from_699_250`), and certifies non-vacuity on `K_4 = (⊤ : SimpleGraph (Fin 4))`
   (`tau = 2`, `nu = 1`).
-/

@[expose] public section

namespace TuzaBound

open Finset

section ArbitraryGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace Construction

variable {edges : Finset (Sym2 V)} (c : Construction edges)

/-- Equation `(3)`: `τ(G) + a ≤ 3n`. -/
theorem first_cover :
    transversalNumber (trianglesOn edges) + c.first.card ≤ 3 * c.initial.card :=
  FirstCover.transversalNumber_add_typeOne_packing_le c.initial_maximum c.first_maximum.1

/-- Sichen Wang's original four estimates (`(3)`, `(4)` with `+3/8 h`, `(5)`, and merged `(6)`). -/
theorem four_covers (r : RefinedConstruction c) :
    (transversalNumber (trianglesOn edges) + c.first.card ≤ 3 * c.initial.card) ∧
    (8 * transversalNumber (trianglesOn edges) + 8 * r.second.card ≤
      12 * c.initial.card + 20 * c.first.card + 12 * c.typeTwo.card +
        3 * (privateRedPages c.specialFamily c.newEdges r.second).card) ∧
    (transversalNumber (trianglesOn edges) + r.second.card + r.third.card ≤
      3 * c.initial.card) ∧
    (4 * transversalNumber (trianglesOn edges) + 4 * c.typeTwo.card +
      (privateRedPages c.specialFamily c.newEdges r.second).card ≤
      12 * c.initial.card + 9 * r.second.card + 6 * r.third.card) :=
  ⟨c.first_cover, TwoLayer.random_cover c r.second_maximum.1, c.full_book_cover r,
    c.fourth_cover r.second_maximum r.third_maximum⟩

/-- The five simultaneous transversal estimates `(3)`, `(4')`, `(5)`, `(6a)`, and `(6c)`
for the same choices of `P, A, P', Q, Q_1`. -/
theorem five_covers (r : RefinedConstruction c) :
    (transversalNumber (trianglesOn edges) + c.first.card ≤ 3 * c.initial.card) ∧
    (4 * transversalNumber (trianglesOn edges) + 4 * r.second.card ≤
      6 * c.initial.card + 10 * c.first.card + 6 * c.typeTwo.card +
        (privateRedPages c.specialFamily c.newEdges r.second).card) ∧
    (transversalNumber (trianglesOn edges) + r.second.card + r.third.card ≤
      3 * c.initial.card) ∧
    (transversalNumber (trianglesOn edges) + c.typeTwo.card + 2 * r.third.card +
      (privateRedPages c.specialFamily c.newEdges r.second).card ≤
      3 * c.initial.card + 3 * r.second.card +
        (privateRedPages (residual c.specialFamily (blueEdges c.newEdges r.second))
          c.newEdges r.third).card) ∧
    (3 * transversalNumber (trianglesOn edges) + 3 * c.typeTwo.card +
      2 * (privateRedPages (residual c.specialFamily (blueEdges c.newEdges r.second))
        c.newEdges r.third).card ≤
      9 * c.initial.card + 6 * r.second.card + 8 * r.third.card) :=
  ⟨c.first_cover,
   c.helper_arborescence_random_cover r,
   c.full_book_cover r,
   (c.unmerged_colored_covers r).1,
   (c.unmerged_colored_covers r).2⟩

/-- Strengthened integer combination retaining the positive private-spine slacks `7 * h + 28 * h_1`. -/
theorem bound_with_private_slack (r : RefinedConstruction c) :
    500 * transversalNumber (trianglesOn edges) +
      7 * (privateRedPages c.specialFamily c.newEdges r.second).card +
      28 * (privateRedPages (residual c.specialFamily (blueEdges c.newEdges r.second))
        c.newEdges r.third).card ≤
      1398 * c.initial.card := by
  obtain ⟨hfirst, hcut, hbooks, hcolA, hcolC⟩ := c.five_covers r
  exact five_bounds_arithmetic hfirst hcut hbooks hcolA hcolC

/-- Cleared-denominator `699 / 250` bound on `(c, r)`. -/
theorem bound_with_residual (r : RefinedConstruction c) :
    250 * transversalNumber (trianglesOn edges) ≤ 699 * c.initial.card := by
  obtain ⟨hfirst, hcut, hbooks, hcolA, hcolC⟩ := c.five_covers r
  exact five_bounds_arithmetic_250_699 hfirst hcut hbooks hcolA hcolC

/-- The six simultaneous elementary transversal estimates `(3)`, unrelaxed `(4'')`, `(5)`,
opposite-elimination `(5'')`, `(6a)`, and `(6b)` on `(c, r)`. -/
theorem six_covers_81_29 (r : RefinedConstruction c) :
    (transversalNumber (trianglesOn edges) + c.first.card ≤ 3 * c.initial.card) ∧
    (4 * transversalNumber (trianglesOn edges) + 4 * r.second.card ≤
      6 * c.initial.card + 10 * c.first.card + 6 * c.typeTwo.card +
        (HelperArborescence.helperRoots c r.second_maximum.1).card) ∧
    (transversalNumber (trianglesOn edges) + r.second.card + r.third.card ≤
      3 * c.initial.card) ∧
    (transversalNumber (trianglesOn edges) + 2 * r.second.card ≤
      3 * c.initial.card +
        (HelperArborescence.helperRoots c r.second_maximum.1).card +
        2 * (OppositeElimination.privZeroPages c r.second_maximum.1).card) ∧
    (transversalNumber (trianglesOn edges) + c.typeTwo.card + 2 * r.third.card +
      (privateRedPages c.specialFamily c.newEdges r.second).card ≤
      3 * c.initial.card + 3 * r.second.card +
        (privateRedPages (residual c.specialFamily (blueEdges c.newEdges r.second))
          c.newEdges r.third).card) ∧
    (transversalNumber (trianglesOn edges) + c.typeTwo.card +
      (privateRedPages (residual c.specialFamily (blueEdges c.newEdges r.second))
        c.newEdges r.third).card ≤
      3 * c.initial.card + 2 * r.second.card + 3 * r.third.card) :=
  ⟨c.first_cover,
   c.helper_arborescence_random_cover_unrelaxed r,
   c.full_book_cover r,
   c.opposite_elimination_cover r,
   c.unmerged_cover_6a r,
   c.unmerged_cover_6b r⟩

/-- Strengthened `81 / 29` integer combination retaining the residual private-spine slack `2 * h_1`:
`29 * τ(G) + 2 * h_1 ≤ 81 * n`. -/
theorem bound_81_29_with_slack (r : RefinedConstruction c) :
    29 * transversalNumber (trianglesOn edges) +
      2 * (privateRedPages (residual c.specialFamily (blueEdges c.newEdges r.second))
        c.newEdges r.third).card ≤
      81 * c.initial.card := by
  obtain ⟨hb3, hb4pp, hb5, hb5pp, hb6a, hb6b⟩ := c.six_covers_81_29 r
  exact six_bounds_arithmetic_29_81 (c.helperRoots_add_privZeroPages_card r)
    hb3 hb4pp hb5 hb5pp hb6a hb6b

/-- Cleared-denominator `81 / 29` bound on `(c, r)`: `29 * τ(G) ≤ 81 * n`. -/
theorem bound_81_29 (r : RefinedConstruction c) :
    29 * transversalNumber (trianglesOn edges) ≤ 81 * c.initial.card := by
  obtain ⟨hb3, hb4pp, hb5, hb5pp, hb6a, hb6b⟩ := c.six_covers_81_29 r
  exact six_bounds_arithmetic_29_81_simple (c.helperRoots_add_privZeroPages_card r)
    hb3 hb4pp hb5 hb5pp hb6a hb6b

end Construction

/-- The `81 / 29` bound for the triangle family of any finite edge set. -/
theorem triangles_bound_81_29 (edges : Finset (Sym2 V)) :
    29 * transversalNumber (trianglesOn edges) ≤ 81 * packingNumber (trianglesOn edges) := by
  obtain ⟨c⟩ := exists_construction edges
  obtain ⟨r⟩ := exists_refinedConstruction c
  have h := c.bound_81_29 r
  rw [c.initial_maximum.card_eq] at h
  exact h

/-- **Theorem 1.2 (Natural-Number Form)**: Every finite simple graph `G` satisfies
`29 * τ(G) ≤ 81 * ν(G)`. -/
theorem tuza_bound_81_29_nat (G : SimpleGraph V) : 29 * tau G ≤ 81 * nu G :=
  triangles_bound_81_29 (graphEdges G)

/-- **Theorem 1.2 (Rational Form)**: Every finite simple graph `G` satisfies
`τ(G) ≤ (81 / 29) * ν(G) ≈ 2.79310345 * ν(G)`. -/
theorem tuza_bound_81_29 (G : SimpleGraph V) : (tau G : ℚ) ≤ (81 / 29 : ℚ) * nu G := by
  have h : (29 : ℚ) * tau G ≤ 81 * nu G := by exact_mod_cast tuza_bound_81_29_nat G
  linarith

/-- **Theorem 1.2 (Explicit Transversal Witness)**: Every finite simple graph `G` has an edge subset
`C ⊆ E(G)` meeting every triangle of `G` with `29 * |C| ≤ 81 * ν(G)`. -/
theorem exists_small_triangle_transversal_81_29 (G : SimpleGraph V) :
    ∃ C : Finset (Sym2 V), C ⊆ graphEdges G ∧
      (∀ u v w, G.Adj u v → G.Adj u w → G.Adj v w →
        s(u, v) ∈ C ∨ s(u, w) ∈ C ∨ s(v, w) ∈ C) ∧
      29 * C.card ≤ 81 * nu G := by
  obtain ⟨C, hsub, hcover, hcard⟩ := exists_graph_minimumCover G
  exact ⟨C, hsub, (graph_cover_iff_adj G C).mp hcover, hcard.symm ▸ tuza_bound_81_29_nat G⟩

/-- **Corollary (`bound_699_250_from_81_29`)**: `250 * τ(G) ≤ 699 * ν(G)` follows
immediately from `29 * τ(G) ≤ 81 * ν(G)` since `250 * 81 = 20250 ≤ 20271 = 29 * 699`. -/
theorem bound_699_250_from_81_29 (G : SimpleGraph V) : 250 * tau G ≤ 699 * nu G := by
  have h := tuza_bound_81_29_nat G
  omega

/-- The `699 / 250` bound for the triangle family of any finite edge set. -/
theorem triangles_bound (edges : Finset (Sym2 V)) :
    250 * transversalNumber (trianglesOn edges) ≤ 699 * packingNumber (trianglesOn edges) := by
  obtain ⟨c⟩ := exists_construction edges
  obtain ⟨r⟩ := exists_refinedConstruction c
  have h := c.bound_with_residual r
  rw [c.initial_maximum.card_eq] at h
  exact h

/-- **Theorem 1 (Natural-Number Form)**: Every finite simple graph `G` satisfies
`250 * τ(G) ≤ 699 * ν(G)`. -/
theorem tuza_bound_nat (G : SimpleGraph V) : 250 * tau G ≤ 699 * nu G :=
  triangles_bound (graphEdges G)

/-- **Theorem 1 (Rational Form)**: Every finite simple graph `G` satisfies
`τ(G) ≤ (699 / 250) * ν(G) = 2.796 * ν(G)`. -/
theorem tuza_bound (G : SimpleGraph V) : (tau G : ℚ) ≤ (699 / 250 : ℚ) * nu G := by
  have h : (250 : ℚ) * tau G ≤ 699 * nu G := by exact_mod_cast tuza_bound_nat G
  linarith

/-- **Theorem 1 (Explicit Transversal Witness)**: Every finite simple graph `G` has an edge subset
`C ⊆ E(G)` meeting every triangle of `G` with `250 * |C| ≤ 699 * ν(G)`. -/
theorem exists_small_triangle_transversal (G : SimpleGraph V) :
    ∃ C : Finset (Sym2 V), C ⊆ graphEdges G ∧
      (∀ u v w, G.Adj u v → G.Adj u w → G.Adj v w →
        s(u, v) ∈ C ∨ s(u, w) ∈ C ∨ s(v, w) ∈ C) ∧
      250 * C.card ≤ 699 * nu G := by
  obtain ⟨C, hsub, hcover, hcard⟩ := exists_graph_minimumCover G
  exact ⟨C, hsub, (graph_cover_iff_adj G C).mp hcover, hcard.symm ▸ tuza_bound_nat G⟩

/-- **Corollary (`wang_bound_from_699_250`)**: Sichen Wang's `59 * τ(G) ≤ 165 * ν(G)` follows
immediately from `250 * τ(G) ≤ 699 * ν(G)` since `59 * 699 = 41241 ≤ 41250 = 165 * 250`. -/
theorem wang_bound_from_699_250 (G : SimpleGraph V) : 59 * tau G ≤ 165 * nu G := by
  have h := tuza_bound_nat G
  omega

end ArbitraryGraph

/-! ## Non-Vacuity Witnesses on `K_4 = (⊤ : SimpleGraph (Fin 4))` -/

/-- Any two triangles on `Fin 4` share at least two vertices and hence a common edge. -/
theorem complete4_triangles_not_disjoint {T₁ T₂ : Finset (Sym2 (Fin 4))}
    (h₁ : T₁ ∈ graphTriangles (⊤ : SimpleGraph (Fin 4)))
    (h₂ : T₂ ∈ graphTriangles (⊤ : SimpleGraph (Fin 4))) :
    ¬ Disjoint T₁ T₂ := by
  obtain ⟨a₁, b₁, c₁, hab₁, hac₁, hbc₁, rfl⟩ := mem_graphTriangles_iff.mp h₁
  obtain ⟨a₂, b₂, c₂, hab₂, hac₂, hbc₂, rfl⟩ := mem_graphTriangles_iff.mp h₂
  let V₁ : Finset (Fin 4) := {a₁, b₁, c₁}
  let V₂ : Finset (Fin 4) := {a₂, b₂, c₂}
  have hc₁ : V₁.card = 3 := by
    simp [V₁, hab₁.ne, hac₁.ne, hbc₁.ne]
  have hc₂ : V₂.card = 3 := by
    simp [V₂, hab₂.ne, hac₂.ne, hbc₂.ne]
  have hcu : (V₁ ∪ V₂).card ≤ 4 :=
    (card_le_univ (V₁ ∪ V₂)).trans_eq (by decide)
  have hsum := card_union_add_card_inter V₁ V₂
  have hinter : 1 < (V₁ ∩ V₂).card := by omega
  obtain ⟨u, hu, v, hv, huv⟩ := one_lt_card.mp hinter
  obtain ⟨hu₁, hu₂⟩ := mem_inter.mp hu
  obtain ⟨hv₁, hv₂⟩ := mem_inter.mp hv
  have mem_tri {x y z : Fin 4} (hu' : u ∈ ({x, y, z} : Finset (Fin 4)))
      (hv' : v ∈ ({x, y, z} : Finset (Fin 4))) :
      s(u, v) ∈ triangleEdges x y z := by
    simp only [mem_insert, mem_singleton] at hu' hv'
    rcases hu' with rfl | rfl | rfl <;> rcases hv' with rfl | rfl | rfl <;>
      try exact (huv rfl).elim
    all_goals simp [triangleEdges, Sym2.eq_swap]
  intro hdisj
  exact disjoint_left.mp hdisj (mem_tri hu₁ hv₁) (mem_tri hu₂ hv₂)

/-- Non-vacuity check: `ν(K_4) = 1`. -/
theorem nu_complete4 : nu (⊤ : SimpleGraph (Fin 4)) = 1 := by
  let K4 : SimpleGraph (Fin 4) := ⊤
  have hT₀ : triangleEdges (0 : Fin 4) 1 2 ∈ graphTriangles K4 :=
    mem_graphTriangles_iff.mpr ⟨0, 1, 2, by decide, by decide, by decide, rfl⟩
  have hpack₁ : IsPacking (graphTriangles K4) {triangleEdges 0 1 2} :=
    ⟨singleton_subset_iff.mpr hT₀, by simp [Set.Pairwise]⟩
  have hge : 1 ≤ nu K4 := (le_nu_iff K4 1).mpr ⟨{triangleEdges 0 1 2}, hpack₁, by simp⟩
  have hle : nu K4 ≤ 1 := by
    change (maximumPacking (graphTriangles K4)).card ≤ 1
    apply card_le_one.mpr
    intro T₁ h₁ T₂ h₂
    by_contra hne
    have hspec := (maximumPacking_spec (graphTriangles K4)).1
    exact complete4_triangles_not_disjoint (hspec.1 h₁) (hspec.1 h₂) (hspec.2 h₁ h₂ hne)
  exact Nat.le_antisymm hle hge

/-- Non-vacuity check: `τ(K_4) = 2` (attaining Tuza's `τ = 2ν` upper bound at `ν = 1`). -/
theorem tau_complete4 : tau (⊤ : SimpleGraph (Fin 4)) = 2 := by
  let K4 : SimpleGraph (Fin 4) := ⊤
  let C₀ : Finset (Sym2 (Fin 4)) := {s(0, 1), s(2, 3)}
  have hcov2_dec : ∀ u v w : Fin 4, u ≠ v → u ≠ w → v ≠ w →
      (s(u, v) = s(0, 1) ∨ s(u, v) = s(2, 3)) ∨
      (s(u, w) = s(0, 1) ∨ s(u, w) = s(2, 3)) ∨
      (s(v, w) = s(0, 1) ∨ s(v, w) = s(2, 3)) := by decide
  have hC₀_cov : IsCover (graphTriangles K4) C₀ := by
    apply (graph_cover_iff_adj K4 C₀).mpr
    intro u v w huv huw hvw
    rcases hcov2_dec u v w huv.ne huw.ne hvw.ne with h | h | h
    · exact Or.inl (by simpa [C₀] using h)
    · exact Or.inr (Or.inl (by simpa [C₀] using h))
    · exact Or.inr (Or.inr (by simpa [C₀] using h))
  have hC₀_card : C₀.card ≤ 2 := by decide
  have hle : tau K4 ≤ 2 := hC₀_cov.number_le.trans hC₀_card
  obtain ⟨C, _, hC, hcard⟩ := exists_graph_minimumCover K4
  have hno1 : ∀ a b : Fin 4, ¬ (∀ u v w : Fin 4, u ≠ v → u ≠ w → v ≠ w →
      s(u, v) = s(a, b) ∨ s(u, w) = s(a, b) ∨ s(v, w) = s(a, b)) := by decide
  have hge : 2 ≤ tau K4 := by
    by_contra hlt
    have hc01 : C.card = 0 ∨ C.card = 1 := by omega
    rcases hc01 with hc0 | hc1
    · have hempty : C = ∅ := card_eq_zero.mp hc0
      subst hempty
      have hT₀ : triangleEdges (0 : Fin 4) 1 2 ∈ graphTriangles K4 :=
        mem_graphTriangles_iff.mpr ⟨0, 1, 2, by decide, by decide, by decide, rfl⟩
      obtain ⟨e, he⟩ := hC _ hT₀
      simp at he
    · obtain ⟨e, heSing⟩ := card_eq_one.mp hc1
      subst heSing
      revert hC
      refine Sym2.inductionOn e (fun a b hCsing => ?_)
      have hadj := (graph_cover_iff_adj K4 {s(a, b)}).mp hCsing
      apply hno1 a b
      intro u v w huv huw hvw
      have hor := hadj u v w (by simpa [K4] using huv)
        (by simpa [K4] using huw) (by simpa [K4] using hvw)
      simpa using hor
  exact Nat.le_antisymm hle hge

end TuzaBound
