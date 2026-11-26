/-
Copyright (c) 2026 Sichen Wang, Tyler B. Hughes. All rights reserved.
Released under MIT license as described in the file LICENSE.
Adapted and extended from https://github.com/sichen-wang/tuza-lean (Lean v4.32.0 -> v4.35.0, namespace TuzaBound).
-/
module

public import TuzaBound.Construction.Setup
public import TuzaBound.Construction.BookCover
public import TuzaBound.Colored.Covers

/-!
The colored covers of the full graph:
- Sichen Wang's merged equation (6) (`fourth_cover`);
- **Lemma 1.2 (`unmerged_colored_covers`)**: keeping equations `(6a)` and `(6c)` unmerged
  simultaneously on the same `(c : Construction edges)` and `(r : RefinedConstruction c)`.
-/

@[expose] public section

namespace TuzaBound
namespace Construction

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {edges : Finset (Sym2 V)}

/-- Any cover `D` of `c.specialFamily` extends via `E(A) ∪ B(P')` to a cover `C` of `G`
satisfying `C.card + b ≤ 3n + D.card`. -/
theorem exists_lifted_special_cover (c : Construction edges) {D : Finset (Sym2 V)}
    (hD : IsCover c.specialFamily D) :
    ∃ C, IsCover (trianglesOn edges) C ∧
      C.card + c.typeTwo.card ≤ 3 * c.initial.card + D.card := by
  have hDres :
      IsCover (residual (trianglesOn c.remainingEdges) (support c.rest ∩ c.old)) D := by
    rw [← c.specialFamily_eq_residual]
    exact hD
  have hremaining := cover_union_residual hDres
  have hremainingRes : IsCover (residual (trianglesOn edges) (support c.first))
      ((support c.rest ∩ c.old) ∪ D) := by
    rw [← trianglesOn_sdiff edges (support c.first)]
    exact hremaining
  let C := support c.first ∪ ((support c.rest ∩ c.old) ∪ D)
  have hC : IsCover (trianglesOn edges) C := cover_union_residual hremainingRes
  have hCcard : C.card ≤ (support c.first).card + (support c.rest ∩ c.old).card + D.card := by
    calc
      C.card ≤ (support c.first).card + ((support c.rest ∩ c.old) ∪ D).card :=
        card_union_le _ _
      _ ≤ (support c.first).card + ((support c.rest ∩ c.old).card + D.card) :=
        Nat.add_le_add_left (card_union_le _ _) _
      _ = (support c.first).card + (support c.rest ∩ c.old).card + D.card := by omega
  have hfirst : (support c.first).card = 3 * c.first.card :=
    c.first_packing.card_support_uniform (fun _ hT => trianglesOn_card (c.first_packing.1 hT))
  have hrest : (support c.rest).card = 3 * c.rest.card :=
    c.rest_packing.card_support_uniform (fun _ hT => trianglesOn_card (c.rest_packing.1 hT))
  have hnew : (support c.rest \ c.old).card = c.typeTwo.card := c.card_newEdges
  have hsplit := card_sdiff_add_card_inter (support c.rest) c.old
  have hpack := c.first_rest_card_le
  exact ⟨C, hC, by omega⟩

theorem transversalNumber_le_add_specialFamily (c : Construction edges) :
    transversalNumber (trianglesOn edges) + c.typeTwo.card ≤
      3 * c.initial.card + transversalNumber c.specialFamily := by
  obtain ⟨D, hD, hDcard⟩ := exists_minimumCover c.specialFamily
    (fun _ hT => c.specialFamily_colored.member_nonempty hT)
  obtain ⟨C, hC, hCcard⟩ := c.exists_lifted_special_cover hD
  have hbound := hC.number_le
  omega

/-- Explicit cover witness for equation `(6a)`: `|C| + b + 2d + h ≤ 3n + 3c + h_1`. -/
theorem exists_unmerged_cover_6a (c : Construction edges) (r : RefinedConstruction c) :
    ∃ C, IsCover (trianglesOn edges) C ∧
      C.card + c.typeTwo.card + 2 * r.third.card +
        (privateRedPages c.specialFamily c.newEdges r.second).card ≤
      3 * c.initial.card + 3 * r.second.card +
        (privateRedPages (residual c.specialFamily (blueEdges c.newEdges r.second))
          c.newEdges r.third).card := by
  obtain ⟨D, hD, hDcard⟩ := exists_first_colored_cover r.second_maximum r.third_maximum.1
    (Subset.refl _)
  change D.card + 2 * r.third.card +
      (privateRedPages c.specialFamily c.newEdges r.second).card ≤
    3 * r.second.card +
      (privateRedPages (residual c.specialFamily (blueEdges c.newEdges r.second))
        c.newEdges r.third).card at hDcard
  obtain ⟨C, hC, hCcard⟩ := c.exists_lifted_special_cover hD
  exact ⟨C, hC, by omega⟩

/-- Explicit cover witness for equation `(6c)`: `3 * |C| + 3b + 2h_1 ≤ 9n + 6c + 8d`. -/
theorem exists_unmerged_cover_6c (c : Construction edges) (r : RefinedConstruction c) :
    ∃ C, IsCover (trianglesOn edges) C ∧
      3 * C.card + 3 * c.typeTwo.card +
        2 * (privateRedPages (residual c.specialFamily (blueEdges c.newEdges r.second))
          c.newEdges r.third).card ≤
      9 * c.initial.card + 6 * r.second.card + 8 * r.third.card := by
  obtain ⟨D, hD, hDcard⟩ := exists_minimumCover c.specialFamily
    (fun _ hT => c.specialFamily_colored.member_nonempty hT)
  have hrec : 3 * transversalNumber c.specialFamily +
      2 * (privateRedPages (residual c.specialFamily (blueEdges c.newEdges r.second))
        c.newEdges r.third).card ≤ 6 * r.second.card + 8 * r.third.card :=
    recursive_colored_cover r.second_maximum r.third_maximum
  obtain ⟨C, hC, hCcard⟩ := c.exists_lifted_special_cover hD
  exact ⟨C, hC, by omega⟩

/-- Equation `(6a)` on `(c, r)`: `τ(G) + b + 2d + h ≤ 3n + 3c + h_1`. -/
theorem unmerged_cover_6a (c : Construction edges) (r : RefinedConstruction c) :
    transversalNumber (trianglesOn edges) + c.typeTwo.card + 2 * r.third.card +
      (privateRedPages c.specialFamily c.newEdges r.second).card ≤
    3 * c.initial.card + 3 * r.second.card +
      (privateRedPages (residual c.specialFamily (blueEdges c.newEdges r.second))
        c.newEdges r.third).card := by
  have hfirst : transversalNumber c.specialFamily + 2 * r.third.card +
      (privateRedPages c.specialFamily c.newEdges r.second).card ≤
    3 * r.second.card +
      (privateRedPages (residual c.specialFamily (blueEdges c.newEdges r.second))
        c.newEdges r.third).card :=
    first_colored_cover r.second_maximum r.third_maximum.1 (Subset.refl _)
  have hlift := c.transversalNumber_le_add_specialFamily
  omega

/-- Equation `(6c)` on `(c, r)`: `3 * τ(G) + 3b + 2h_1 ≤ 9n + 6c + 8d`. -/
theorem unmerged_cover_6c (c : Construction edges) (r : RefinedConstruction c) :
    3 * transversalNumber (trianglesOn edges) + 3 * c.typeTwo.card +
      2 * (privateRedPages (residual c.specialFamily (blueEdges c.newEdges r.second))
        c.newEdges r.third).card ≤
    9 * c.initial.card + 6 * r.second.card + 8 * r.third.card := by
  have hrec : 3 * transversalNumber c.specialFamily +
      2 * (privateRedPages (residual c.specialFamily (blueEdges c.newEdges r.second))
        c.newEdges r.third).card ≤ 6 * r.second.card + 8 * r.third.card :=
    recursive_colored_cover r.second_maximum r.third_maximum
  have hlift := c.transversalNumber_le_add_specialFamily
  omega

/-- **Lemma 1.2 (`unmerged_colored_covers`)**: simultaneous validity of the two unmerged
Lemma 2.3 bounds `(6a)` and `(6c)` on the same `(c : Construction edges)` and
`(r : RefinedConstruction c)`. -/
theorem unmerged_colored_covers (c : Construction edges) (r : RefinedConstruction c) :
    (transversalNumber (trianglesOn edges) + c.typeTwo.card + 2 * r.third.card +
      (privateRedPages c.specialFamily c.newEdges r.second).card ≤
    3 * c.initial.card + 3 * r.second.card +
      (privateRedPages (residual c.specialFamily (blueEdges c.newEdges r.second))
        c.newEdges r.third).card) ∧
    (3 * transversalNumber (trianglesOn edges) + 3 * c.typeTwo.card +
      2 * (privateRedPages (residual c.specialFamily (blueEdges c.newEdges r.second))
        c.newEdges r.third).card ≤
    9 * c.initial.card + 6 * r.second.card + 8 * r.third.card) :=
  ⟨c.unmerged_cover_6a r, c.unmerged_cover_6c r⟩

/-- Explicit cover witness for elementary non-recursive equation `(6b)`:
`|C| + b + h_1 ≤ 3n + 2c + 3d`. -/
theorem exists_unmerged_cover_6b (c : Construction edges) (r : RefinedConstruction c) :
    ∃ C, IsCover (trianglesOn edges) C ∧
      C.card + c.typeTwo.card +
        (privateRedPages (residual c.specialFamily (blueEdges c.newEdges r.second))
          c.newEdges r.third).card ≤
      3 * c.initial.card + 2 * r.second.card + 3 * r.third.card := by
  obtain ⟨D, hD, hDcard⟩ := exists_minimumCover c.specialFamily
    (fun _ hT => c.specialFamily_colored.member_nonempty hT)
  have hsec : transversalNumber c.specialFamily +
      (privateRedPages (residual c.specialFamily (blueEdges c.newEdges r.second))
        c.newEdges r.third).card ≤ 2 * r.second.card + 3 * r.third.card :=
    second_colored_cover c.specialFamily_colored r.second_maximum.1 r.third_maximum
  obtain ⟨C, hC, hCcard⟩ := c.exists_lifted_special_cover hD
  exact ⟨C, hC, by omega⟩

/-- Elementary non-recursive equation `(6b)` on `(c, r)`:
`τ(G) + b + h_1 ≤ 3n + 2c + 3d`. -/
theorem unmerged_cover_6b (c : Construction edges) (r : RefinedConstruction c) :
    transversalNumber (trianglesOn edges) + c.typeTwo.card +
      (privateRedPages (residual c.specialFamily (blueEdges c.newEdges r.second))
        c.newEdges r.third).card ≤
    3 * c.initial.card + 2 * r.second.card + 3 * r.third.card := by
  have hsec : transversalNumber c.specialFamily +
      (privateRedPages (residual c.specialFamily (blueEdges c.newEdges r.second))
        c.newEdges r.third).card ≤ 2 * r.second.card + 3 * r.third.card :=
    second_colored_cover c.specialFamily_colored r.second_maximum.1 r.third_maximum
  have hlift := c.transversalNumber_le_add_specialFamily
  omega

/-- Simultaneous validity of the two elementary non-recursive Lemma 2.3 bounds
`(6a)` and `(6b)` on `(c, r)`. -/
theorem elementary_colored_covers (c : Construction edges) (r : RefinedConstruction c) :
    (transversalNumber (trianglesOn edges) + c.typeTwo.card + 2 * r.third.card +
      (privateRedPages c.specialFamily c.newEdges r.second).card ≤
    3 * c.initial.card + 3 * r.second.card +
      (privateRedPages (residual c.specialFamily (blueEdges c.newEdges r.second))
        c.newEdges r.third).card) ∧
    (transversalNumber (trianglesOn edges) + c.typeTwo.card +
      (privateRedPages (residual c.specialFamily (blueEdges c.newEdges r.second))
        c.newEdges r.third).card ≤
    3 * c.initial.card + 2 * r.second.card + 3 * r.third.card) :=
  ⟨c.unmerged_cover_6a r, c.unmerged_cover_6b r⟩

/-- Sichen Wang's merged fourth cover (`1/4 * (6a) + 3/4 * (6c)`). -/
theorem exists_fourth_cover (c : Construction edges)
    {Q Q1 : Finset (Finset (Sym2 V))}
    (hQ : IsMaximumPacking c.specialFamily Q)
    (hQ1 : IsMaximumPacking (residual c.specialFamily (blueEdges c.newEdges Q)) Q1) :
    ∃ C, IsCover (trianglesOn edges) C ∧
      4 * C.card + 4 * c.typeTwo.card + (privateRedPages c.specialFamily c.newEdges Q).card
      ≤ 12 * c.initial.card + 9 * Q.card + 6 * Q1.card := by
  classical
  have hcolored :
      4 * transversalNumber c.specialFamily + (privateRedPages c.specialFamily c.newEdges Q).card
      ≤ 9 * Q.card + 6 * Q1.card :=
    colored_refined hQ hQ1 (Subset.refl _)
  obtain ⟨D, hD, hDcard⟩ := exists_minimumCover c.specialFamily
    (fun _ hT => c.specialFamily_colored.member_nonempty hT)
  obtain ⟨C, hC, hCcard⟩ := c.exists_lifted_special_cover hD
  exact ⟨C, hC, by omega⟩

theorem fourth_cover (c : Construction edges)
    {Q Q1 : Finset (Finset (Sym2 V))}
    (hQ : IsMaximumPacking c.specialFamily Q)
    (hQ1 : IsMaximumPacking (residual c.specialFamily (blueEdges c.newEdges Q)) Q1) :
    4 * transversalNumber (trianglesOn edges) + 4 * c.typeTwo.card +
      (privateRedPages c.specialFamily c.newEdges Q).card
      ≤ 12 * c.initial.card + 9 * Q.card + 6 * Q1.card := by
  obtain ⟨C, hC, hcard⟩ := c.exists_fourth_cover hQ hQ1
  have hbound := hC.number_le
  omega

end Construction
end TuzaBound
