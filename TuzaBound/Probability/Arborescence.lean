/-
Copyright (c) 2026 Tyler B. Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Helper-arborescence combinatorics for Lemma 1.1 (`TuzaBound`).
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Tactic

/-!
# Partial-Functional Digraph Basins and Arborescence Secant Sums

For any partial function `next : I → Option I` on a finite index type `I` (encoding a directed
graph of maximum out-degree `≤ 1`) and any set `roots : Finset I` of sinks (`next r = none`),
this module proves:
1. Uniqueness of both sink and path length (`reachIn_sink_unique`), producing an injective
   directed chain `idx : Fin (k + 1) → I` from `r` up to `v` (`exists_chain_from_sink`).
2. Pairwise vertex-disjointness of the ancestor basins `basin next r` across `r ∈ roots`
   (`basin_disjoint`), with `1 ≤ (basin next r).card` (`one_le_card_basin`).
3. Exact arborescence in-degree sum `(∑ v ∈ basin next r, (childrenOf next v).card) + 1 =
   (basin next r).card` (`sum_childrenOf_card`).
4. Convex secant inequality `(1 / 8 : ℚ) - (3 / 32 : ℚ) * k ≤ (1 / 8 : ℚ) * (1 / 4 : ℚ) ^ k`
   (`fourth_pow_secant`) and global expectation saving `∑ i : I, prob i ≤ |I|/2 - |roots|/8`
   (`global_prob_sum_le`).
-/

@[expose] public section

namespace TuzaBound
namespace Arborescence

open Finset
open scoped BigOperators

variable {I : Type*}

/-- `k`-step forward walk along a partial function `next : I → Option I`. -/
def reachIn (next : I → Option I) : ℕ → I → Option I
  | 0, x => some x
  | k + 1, x => (next x).bind (reachIn next k)

/-- If a vertex `x` reaches sinks `r₁, r₂` (`next r = none`) in `k₁` and `k₂` steps,
then both the step counts and the sinks coincide. -/
theorem reachIn_sink_unique {next : I → Option I} {k₁ k₂ : ℕ} {x r₁ r₂ : I}
    (h₁ : reachIn next k₁ x = some r₁) (h₂ : reachIn next k₂ x = some r₂)
    (hs₁ : next r₁ = none) (hs₂ : next r₂ = none) :
    k₁ = k₂ ∧ r₁ = r₂ := by
  induction k₁ generalizing k₂ x with
  | zero =>
    simp only [reachIn, Option.some.injEq] at h₁
    subst h₁
    cases k₂ with
    | zero =>
      simp only [reachIn, Option.some.injEq] at h₂
      exact ⟨rfl, h₂⟩
    | succ m₂ =>
      simp [reachIn, hs₁] at h₂
  | succ m₁ ih =>
    cases hnx : next x with
    | none => simp [reachIn, hnx] at h₁
    | some y =>
      simp only [reachIn, hnx, Option.bind_some] at h₁
      cases k₂ with
      | zero =>
        simp only [reachIn, Option.some.injEq] at h₂
        subst h₂
        simp [hs₂] at hnx
      | succ m₂ =>
        simp only [reachIn, hnx, Option.bind_some] at h₂
        obtain ⟨hm, hr⟩ := ih h₁ h₂
        exact ⟨congrArg Nat.succ hm, hr⟩

/-- Every vertex reaching a sink `r` (`next r = none`) in `k` steps is connected to `r`
by an injective chain `idx : Fin (k + 1) → I` starting at `idx 0 = r` and ending at
`idx (Fin.last k) = v`, with `next (idx t.succ) = some (idx t.castSucc)`. -/
theorem exists_chain_from_sink {next : I → Option I} {k : ℕ} {v r : I}
    (h : reachIn next k v = some r) (hr : next r = none) :
    ∃ idx : Fin (k + 1) → I,
      idx 0 = r ∧
      idx (Fin.last k) = v ∧
      Function.Injective idx ∧
      (∀ s : Fin (k + 1), reachIn next s.val (idx s) = some r) ∧
      (∀ t : Fin k, next (idx t.succ) = some (idx t.castSucc)) := by
  induction k generalizing v with
  | zero =>
    simp only [reachIn, Option.some.injEq] at h
    subst h
    refine ⟨fun _ => v, rfl, rfl, ?_, ?_, ?_⟩
    · intro a b _
      exact Fin.ext (by omega)
    · intro s
      have hs : s.val = 0 := by omega
      rw [hs]
      rfl
    · intro t
      exact Fin.elim0 t
  | succ k ih =>
    cases hnv : next v with
    | none => simp [reachIn, hnv] at h
    | some u =>
      have hu : reachIn next k u = some r := by
        simpa [reachIn, hnv] using h
      obtain ⟨idx₀, h0, hlast, _, hreach₀, hstep₀⟩ := ih hu
      let idx : Fin (k + 2) → I :=
        fun s => if hs : s.val < k + 1 then idx₀ ⟨s.val, hs⟩ else v
      have hcast (s₀ : Fin (k + 1)) : idx s₀.castSucc = idx₀ s₀ := by
        dsimp [idx]
        split_ifs with hs
        · rfl
        · exact (hs s₀.isLt).elim
      have hidxLast : idx (Fin.last (k + 1)) = v := by
        simp [idx]
      have hidx0 : idx 0 = r := by
        have h0eq : (0 : Fin (k + 2)) = (0 : Fin (k + 1)).castSucc := rfl
        rw [h0eq, hcast, h0]
      have hreach : ∀ s : Fin (k + 2), reachIn next s.val (idx s) = some r := by
        intro s
        refine Fin.lastCases ?_ ?_ s
        · simpa [hidxLast] using h
        · intro s₀
          simpa [hcast] using hreach₀ s₀
      have hinj : Function.Injective idx := by
        intro s₁ s₂ heq
        have h₁ := hreach s₁
        have h₂ := heq ▸ hreach s₂
        exact Fin.ext (reachIn_sink_unique h₁ h₂ hr hr).1
      have hstep : ∀ t : Fin (k + 1), next (idx t.succ) = some (idx t.castSucc) := by
        intro t
        refine Fin.lastCases ?_ ?_ t
        · have hsucc : (Fin.last k).succ = Fin.last (k + 1) := rfl
          rw [hsucc, hidxLast, hcast, hlast, hnv]
        · intro t₀
          have hsucc : t₀.castSucc.succ = t₀.succ.castSucc := by
            ext
            rfl
          rw [hsucc, hcast, hcast]
          exact hstep₀ t₀
      exact ⟨idx, hidx0, hidxLast, hinj, hreach, hstep⟩

section Finite

variable [Fintype I] [DecidableEq I]

/-- Ancestor basin of `r` under `next`. -/
noncomputable def basin (next : I → Option I) (r : I) : Finset I := by
  classical
  exact univ.filter (fun v => ∃ k, reachIn next k v = some r)

/-- Direct predecessors (children in the in-arborescence) of `v` under `next`. -/
def childrenOf (next : I → Option I) (v : I) : Finset I :=
  univ.filter (fun j => next j = some v)

omit [DecidableEq I] in
@[simp] theorem mem_basin {next : I → Option I} {r v : I} :
    v ∈ basin next r ↔ ∃ k, reachIn next k v = some r := by
  classical
  simp [basin]

@[simp] theorem mem_childrenOf {next : I → Option I} {v j : I} :
    j ∈ childrenOf next v ↔ next j = some v := by
  simp [childrenOf]

omit [DecidableEq I] in
theorem self_mem_basin (next : I → Option I) (r : I) : r ∈ basin next r :=
  mem_basin.mpr ⟨0, rfl⟩

omit [DecidableEq I] in
theorem one_le_card_basin (next : I → Option I) (r : I) :
    1 ≤ (basin next r).card :=
  card_pos.mpr ⟨r, self_mem_basin next r⟩

omit [DecidableEq I] in
theorem basin_disjoint {next : I → Option I} {r₁ r₂ : I}
    (hs₁ : next r₁ = none) (hs₂ : next r₂ = none) (hne : r₁ ≠ r₂) :
    Disjoint (basin next r₁) (basin next r₂) := by
  apply disjoint_left.mpr
  intro v hv₁ hv₂
  obtain ⟨k₁, hk₁⟩ := mem_basin.mp hv₁
  obtain ⟨k₂, hk₂⟩ := mem_basin.mp hv₂
  exact hne (reachIn_sink_unique hk₁ hk₂ hs₁ hs₂).2

theorem childrenOf_pairwise_disjoint (next : I → Option I) :
    Pairwise (fun v₁ v₂ : I => Disjoint (childrenOf next v₁) (childrenOf next v₂)) := by
  intro v₁ v₂ hne
  apply disjoint_left.mpr
  intro j hj₁ hj₂
  have h₁ := mem_childrenOf.mp hj₁
  have h₂ := mem_childrenOf.mp hj₂
  exact hne (Option.some.inj (h₁.symm.trans h₂))

/-- Every non-root member of `basin next r` is a child of a unique member of `basin next r`,
and conversely every child of a member of `basin next r` lies in `(basin next r).erase r`. -/
theorem biUnion_childrenOf_eq_erase {next : I → Option I} {r : I}
    (hr : next r = none) :
    (basin next r).biUnion (childrenOf next) = (basin next r).erase r := by
  ext j
  constructor
  · intro hj
    obtain ⟨v, hv, hjv⟩ := mem_biUnion.mp hj
    obtain ⟨k, hk⟩ := mem_basin.mp hv
    have hnj : next j = some v := mem_childrenOf.mp hjv
    have hjne : j ≠ r := by
      rintro rfl
      simp [hr] at hnj
    exact mem_erase.mpr ⟨hjne, mem_basin.mpr ⟨k + 1, by simp [reachIn, hnj, hk]⟩⟩
  · intro hj
    obtain ⟨hjne, hjB⟩ := mem_erase.mp hj
    obtain ⟨k, hk⟩ := mem_basin.mp hjB
    cases k with
    | zero =>
      simp only [reachIn, Option.some.injEq] at hk
      exact (hjne hk).elim
    | succ m =>
      cases hnj : next j with
      | none => simp [reachIn, hnj] at hk
      | some v =>
        simp only [reachIn, hnj, Option.bind_some] at hk
        exact mem_biUnion.mpr ⟨v, mem_basin.mpr ⟨m, hk⟩, mem_childrenOf.mpr hnj⟩

/-- In-arborescence degree sum: `∑_{v ∈ T_r} indeg(v) + 1 = |T_r|`. -/
theorem sum_childrenOf_card {next : I → Option I} {r : I}
    (hr : next r = none) :
    (∑ v ∈ basin next r, (childrenOf next v).card) + 1 = (basin next r).card := by
  have hbi : ((basin next r).biUnion (childrenOf next)).card =
      ∑ v ∈ basin next r, (childrenOf next v).card :=
    card_biUnion (fun _ _ _ _ hne => childrenOf_pairwise_disjoint next hne)
  rw [← hbi, biUnion_childrenOf_eq_erase hr]
  exact card_erase_add_one (self_mem_basin next r)

/-- Convex secant bound: `(1/8) * (1/4)^k ≥ 1/8 - (3/32) * k` for every `k : ℕ`,
with equality at `k = 0` and `k = 1`. -/
theorem fourth_pow_secant (k : ℕ) :
    (1 / 8 : ℚ) - (3 / 32 : ℚ) * k ≤ (1 / 8 : ℚ) * (1 / 4 : ℚ) ^ k := by
  match k with
  | 0 => norm_num
  | 1 => norm_num
  | m + 2 =>
    have hpos : (0 : ℚ) ≤ (1 / 8 : ℚ) * (1 / 4 : ℚ) ^ (m + 2) := by positivity
    have hm : (0 : ℚ) ≤ m := Nat.cast_nonneg m
    push_cast
    linarith

/-- Summing `prob v ≤ 1/2 - (1/8) * 4^(-indeg v)` over an arborescence `basin next r`
saves at least `1/8` (`(3/32) + (1/32)*|T_r| ≥ 1/8`). -/
theorem basin_prob_sum_le {next : I → Option I} {r : I} (hr : next r = none)
    (prob : I → ℚ)
    (hprob : ∀ v ∈ basin next r,
      prob v ≤ 1 / 2 - (1 / 8 : ℚ) * (1 / 4 : ℚ) ^ (childrenOf next v).card) :
    ∑ v ∈ basin next r, prob v ≤ (1 / 2 : ℚ) * (basin next r).card - 1 / 8 := by
  have hlin : ∀ v ∈ basin next r,
      prob v ≤ 1 / 2 - ((1 / 8 : ℚ) - (3 / 32 : ℚ) * (childrenOf next v).card) := by
    intro v hv
    have h₁ := hprob v hv
    have h₂ := fourth_pow_secant (childrenOf next v).card
    linarith
  have hsum := sum_le_sum hlin
  have hdeg : (∑ v ∈ basin next r, ((childrenOf next v).card : ℚ)) + 1 =
      ((basin next r).card : ℚ) := by
    exact_mod_cast sum_childrenOf_card hr
  have hone : (1 : ℚ) ≤ (basin next r).card := by
    exact_mod_cast one_le_card_basin next r
  have hrhs :
      (∑ v ∈ basin next r,
        ((1 / 2 : ℚ) - ((1 / 8 : ℚ) - (3 / 32 : ℚ) * (childrenOf next v).card))) =
      (3 / 8 : ℚ) * (basin next r).card +
        (3 / 32 : ℚ) * (∑ v ∈ basin next r, ((childrenOf next v).card : ℚ)) := by
    simp only [sub_sub_eq_add_sub, sum_sub_distrib, sum_add_distrib, sum_const,
      nsmul_eq_mul, ← mul_sum]
    ring
  linarith

/-- Global arborescence expectation bound: summing `prob i` across all `i : I` yields
at most `|I| / 2 - |roots| / 8`. -/
theorem global_prob_sum_le {next : I → Option I} {roots : Finset I}
    (hroots : ∀ r ∈ roots, next r = none)
    (prob : I → ℚ)
    (hhalf : ∀ i : I, prob i ≤ 1 / 2)
    (hbasin : ∀ r ∈ roots, ∀ v ∈ basin next r,
      prob v ≤ 1 / 2 - (1 / 8 : ℚ) * (1 / 4 : ℚ) ^ (childrenOf next v).card) :
    ∑ i : I, prob i ≤ (1 / 2 : ℚ) * Fintype.card I - (1 / 8 : ℚ) * roots.card := by
  classical
  let B := roots.biUnion (basin next)
  have hdisj : (roots : Set I).PairwiseDisjoint (basin next) := by
    intro r₁ hr₁ r₂ hr₂ hne
    exact basin_disjoint (hroots r₁ hr₁) (hroots r₂ hr₂) hne
  have hpart : (univ : Finset I) = B ∪ (univ \ B) := by
    ext i
    by_cases hi : i ∈ B <;> simp [hi]
  have hdBU : Disjoint B (univ \ B) := disjoint_sdiff_self_right
  have hcardU : (Fintype.card I : ℚ) = (B.card : ℚ) + ((univ \ B).card : ℚ) := by
    have hc : (univ : Finset I).card = B.card + (univ \ B).card := by
      conv_lhs => rw [hpart]
      exact card_union_of_disjoint hdBU
    exact_mod_cast hc
  have hBcard : (B.card : ℚ) = ∑ r ∈ roots, ((basin next r).card : ℚ) := by
    have hc : B.card = ∑ r ∈ roots, (basin next r).card := card_biUnion hdisj
    exact_mod_cast hc
  have hsumU : ∑ i : I, prob i = (∑ i ∈ B, prob i) + ∑ i ∈ univ \ B, prob i := by
    conv_lhs => rw [hpart]
    exact sum_union hdBU
  have hsumB : ∑ i ∈ B, prob i = ∑ r ∈ roots, ∑ v ∈ basin next r, prob v :=
    sum_biUnion hdisj
  have hboundB : ∑ r ∈ roots, ∑ v ∈ basin next r, prob v ≤
      ∑ r ∈ roots, ((1 / 2 : ℚ) * (basin next r).card - 1 / 8) :=
    sum_le_sum (fun r hr => basin_prob_sum_le (hroots r hr) prob (hbasin r hr))
  have hrhsB : (∑ r ∈ roots, ((1 / 2 : ℚ) * (basin next r).card - 1 / 8)) =
      (1 / 2 : ℚ) * B.card - (1 / 8 : ℚ) * roots.card := by
    rw [sum_sub_distrib, ← mul_sum, ← hBcard]
    simp only [sum_const, nsmul_eq_mul]
    ring
  have hboundRest : ∑ i ∈ univ \ B, prob i ≤ (1 / 2 : ℚ) * (univ \ B).card := by
    calc
      ∑ i ∈ univ \ B, prob i ≤ ∑ _i ∈ univ \ B, (1 / 2 : ℚ) :=
        sum_le_sum (fun i _ => hhalf i)
      _ = (1 / 2 : ℚ) * (univ \ B).card := by simp [mul_comm]
  linarith

end Finite

end Arborescence
end TuzaBound
