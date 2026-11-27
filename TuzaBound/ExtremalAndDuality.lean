/-
Copyright (c) 2026 Tyler B. Hughes. All rights reserved.
Released under MIT license as described in the file LICENSE.
Exact 81/29 LP duality, conditional structural slices, and extremal tightness families for `TuzaBound`.
-/
module

public import TuzaBound.Main
public import TuzaBound.FixedPoint

/-!
# Exact `81/29` LP Duality, Conditional Structural Slices, and Extremal Tightness Families

Purely additive mathematical strengthening of `TuzaBound`:

1. **Exact `81/29` Infinite-Depth LP Barrier, Primal Uniqueness & Dual Uniqueness**:
   - Extends `FixedPoint.lean` from `699/250` to the full `(3) + (4'') + (5) + (5'') + Lemma 2.3`
     infinite-depth hierarchy (including the blue-edge budget at every depth and the Old-Packing
     Hit-Degree Inequality `n - a ≤ 3m - b - 2 h_hat`).
   - Proves the global full-slack upper bound `29 * t + 45 * (n - a - m) + 2 * u 1 ≤ 81 * n`
     and the `(6c)` variant `87 * t + 135 * (n - a - m) + 4 * p 1 + 2 * u 1 ≤ 243 * n`.
   - Exhibits the matching exact primal extreme ray
     `(n, t, a, m, b, h_hat, h0) = (29, 81, 6, 23, 18, 6, 0)` with `p = u = (6, 0, 0, ...)`,
     shows it satisfies even the hypothetical Tuza-on-`S` inequality `t ≤ 3a + 3m - b + 2 p 0`,
     and proves **exact uniqueness** of BOTH the primal optimal ray (across all depths `r : ℕ`)
     AND the 6-cover dual certificate `(10, 4, 8, 1, 2, 4) / 29`.
2. **Unrelaxed Graph-Level `81/29` Full-Slack Bounds & Conditional Structural Slices**:
   - Retains `3a + 3m` unrelaxed on `(5), (5''), (6a), (6b), (6c)` to prove
     `29 * τ + 45 * (n - (a + m)) + 2 * h_1 ≤ 81 * n` and
     `87 * τ + 135 * (n - (a + m)) + 4 * d + 2 * h_1 ≤ 243 * n` directly on `(c, r)`.
   - Proves exact sharp conditional slices directly on arbitrary finite graphs:
     `h = 0` (`13 * τ + (d - h_1) ≤ 36 * n`), `h_hat = 0` (`101 * τ + 4 * h_1 ≤ 282 * n`,
     strictly beating `81/29` by `3/2929`), `a = 0` (`19 * τ + 2 * h_1 ≤ 51 * n`),
     `c = 0` (`10 * τ ≤ 27 * n`), `b = 0` (`7 * τ ≤ 18 * n`), plus 2-way slices
     (`21/8`, `11/4`, `39/14`).
3. **Unconditional Graph-Theoretic Tightness Families (`k · K_4`, `K_5`, `k · K_5`)**:
   - Proves general additivity `nu (disjointCopy k G) = k * nu G` and
     `tau (disjointCopy k G) = k * tau G` for every finite simple graph `G` and every `k : ℕ`.
   - Proves `nu K_5 = 2` (by vertex-degree parity of `K_5 \ support P`) and `tau K_5 = 4`
     (via Mantel's Cauchy–Schwarz theorem on `Fin 5`).
   - Derives the full infinite Tuza-tight families `tau (disjointK4 k) = 2 * nu (disjointK4 k)`
     and `tau (disjointK5 k) = 2 * nu (disjointK5 k)` for every `k : ℕ`.
-/

@[expose] public section

namespace TuzaBound

open Finset
open scoped BigOperators

/-! ## Section 1: Exact `81/29` Infinite-Depth LP Barrier, Primal Uniqueness & Dual Uniqueness -/

/-- Full unrelaxed infinite-depth LP constraint set for the `81/29` system, combining
`(3)`, unrelaxed `(4'')`, `(5)`, opposite-elimination `(5'')`, the blue-edge budget at every
depth `K : ℕ`, the Old-Packing Hit-Degree Inequality `n - a ≤ 3m - b - 2 h_hat`, and all four
Lemma 2.3 bounds at every depth `r : ℕ`. -/
structure IsValidInfiniteHierarchyPoint8129
    (n t a m b h_hat h0 : ℚ) (p u : ℕ → ℚ) : Prop where
  nonneg_n : 0 ≤ n
  nonneg_t : 0 ≤ t
  nonneg_a : 0 ≤ a
  nonneg_m : 0 ≤ m
  nonneg_b : 0 ≤ b
  nonneg_h_hat : 0 ≤ h_hat
  nonneg_h0 : 0 ≤ h0
  nonneg_p : ∀ r, 0 ≤ p r
  nonneg_u : ∀ r, 0 ≤ u r
  pack_am : a + m ≤ n
  pack_bm : b ≤ m
  pack_p0 : p 0 ≤ b
  split_u0 : h_hat + h0 = u 0
  disj_pu : ∀ r, p (r + 1) + u r ≤ p r
  blue_budget : ∀ K, a + 3 * m - b + bluePrefix p K ≤ 3 * n
  hit_degree : n - a ≤ 3 * m - b - 2 * h_hat
  bound_3 : t ≤ 3 * n - a
  bound_4'' : t ≤ (3 / 2 : ℚ) * n + (5 / 2 : ℚ) * a + (3 / 2 : ℚ) * b - p 0 +
    (1 / 4 : ℚ) * h_hat
  bound_5 : t ≤ 3 * a + 3 * m - p 0 - p 1
  bound_5'' : t ≤ 3 * a + 3 * m - 2 * p 0 + h_hat + 2 * h0
  triv_r : ∀ r, t ≤ 3 * a + 3 * m - b + bluePrefix p r + 3 * p r - u r
  col_r : ∀ r, t ≤ 3 * a + 3 * m - b + bluePrefix p r + (8 / 3 : ℚ) * p r - (2 / 3 : ℚ) * u r
  book2_r : ∀ r, t ≤ 3 * a + 3 * m - b + bluePrefix p r + 3 * p r - 2 * p (r + 1) + u (r + 1) - u r
  book3_r : ∀ r, t ≤ 3 * a + 3 * m - b + bluePrefix p r + 3 * p r - p (r + 1) - p (r + 2) - u r

/-- Exact full-slack `81/29` LP upper bound from weights `(10, 4, 8, 1, 2, 4)` on
`(3), (4''), (5), (5''), (6a), (6b)`: `29 * t + 45 * (n - a - m) + 2 * u 1 ≤ 81 * n`. -/
theorem infinite_depth_lp_81_29_upper_with_slack
    {n t a m b h_hat h0 : ℚ} {p u : ℕ → ℚ}
    (h : IsValidInfiniteHierarchyPoint8129 n t a m b h_hat h0 p u) :
    29 * t + 45 * (n - a - m) + 2 * u 1 ≤ 81 * n := by
  have hsplit := h.split_u0
  have h3 := h.bound_3
  have h4 := h.bound_4''
  have h5 := h.bound_5
  have h5'' := h.bound_5''
  have h6a : t ≤ 3 * a + 3 * m - b + 3 * p 0 - 2 * p 1 + u 1 - u 0 := by
    simpa [bluePrefix_zero] using h.book2_r 0
  have h6b : t ≤ 3 * a + 3 * m - b + 2 * p 0 + 3 * p 1 - u 1 := by
    have ht1 := h.triv_r 1
    rw [bluePrefix_succ, bluePrefix_zero] at ht1
    linarith
  linarith

/-- Recursive-`(6c)` variant retaining positive slack on BOTH `p 1` (`d`) and `u 1` (`h_1`):
`87 * t + 135 * (n - a - m) + 4 * p 1 + 2 * u 1 ≤ 243 * n`. -/
theorem infinite_depth_lp_81_29_upper_with_d_slack
    {n t a m b h_hat h0 : ℚ} {p u : ℕ → ℚ}
    (h : IsValidInfiniteHierarchyPoint8129 n t a m b h_hat h0 p u) :
    87 * t + 135 * (n - a - m) + 4 * p 1 + 2 * u 1 ≤ 243 * n := by
  have hsplit := h.split_u0
  have h3 := h.bound_3
  have h4 := h.bound_4''
  have h5 := h.bound_5
  have h5'' := h.bound_5''
  have h6a : t ≤ 3 * a + 3 * m - b + 3 * p 0 - 2 * p 1 + u 1 - u 0 := by
    simpa [bluePrefix_zero] using h.book2_r 0
  have h6c : t ≤ 3 * a + 3 * m - b + 2 * p 0 + (8 / 3 : ℚ) * p 1 - (2 / 3 : ℚ) * u 1 := by
    have hc1 := h.col_r 1
    rw [bluePrefix_succ, bluePrefix_zero] at hc1
    linarith
  linarith

/-- Universal `81/29` upper bound across the entire infinite-depth hierarchy. -/
theorem infinite_depth_lp_81_29_upper
    {n t a m b h_hat h0 : ℚ} {p u : ℕ → ℚ}
    (h : IsValidInfiniteHierarchyPoint8129 n t a m b h_hat h0 p u) :
    t ≤ (81 / 29 : ℚ) * n := by
  have hslack := infinite_depth_lp_81_29_upper_with_slack h
  have ham := h.pack_am
  have hu1 := h.nonneg_u 1
  linarith

/-- Primal extreme-ray packing sequence `(6, 0, 0, ...)` at `n = 29`. -/
def primalP8129 : ℕ → ℚ
  | 0 => 6
  | _ + 1 => 0

/-- Primal extreme-ray private-spine sequence `(6, 0, 0, ...)` at `n = 29`. -/
def primalU8129 : ℕ → ℚ
  | 0 => 6
  | _ + 1 => 0

theorem bluePrefix_primalP8129_succ (k : ℕ) : bluePrefix primalP8129 (k + 1) = 12 := by
  induction k with
  | zero =>
    rw [bluePrefix_succ, bluePrefix_zero, primalP8129]
    norm_num
  | succ k ih =>
    have hstep : bluePrefix primalP8129 (k + 2) =
        bluePrefix primalP8129 (k + 1) + 2 * primalP8129 (k + 1) :=
      bluePrefix_succ primalP8129 (k + 1)
    rw [hstep, ih, primalP8129]
    norm_num

/-- Exact primal feasibility of the extreme ray
`(n, t, a, m, b, h_hat, h0) = (29, 81, 6, 23, 18, 6, 0)` with `p = u = (6, 0, 0, ...)`
across ALL depths `r : ℕ`, the blue-edge budget at every depth, and the hit-degree inequality. -/
theorem infinite_depth_lp_81_29_attained :
    IsValidInfiniteHierarchyPoint8129 29 81 6 23 18 6 0 primalP8129 primalU8129 := by
  refine
    { nonneg_n := by norm_num
      nonneg_t := by norm_num
      nonneg_a := by norm_num
      nonneg_m := by norm_num
      nonneg_b := by norm_num
      nonneg_h_hat := by norm_num
      nonneg_h0 := by norm_num
      nonneg_p := fun r => by cases r <;> norm_num [primalP8129]
      nonneg_u := fun r => by cases r <;> norm_num [primalU8129]
      pack_am := by norm_num
      pack_bm := by norm_num
      pack_p0 := by norm_num [primalP8129]
      split_u0 := by norm_num [primalU8129]
      disj_pu := fun r => by cases r <;> norm_num [primalP8129, primalU8129]
      blue_budget := fun K => by
        cases K with
        | zero => norm_num [bluePrefix_zero]
        | succ k => norm_num [bluePrefix_primalP8129_succ]
      hit_degree := by norm_num
      bound_3 := by norm_num
      bound_4'' := by norm_num [primalP8129]
      bound_5 := by norm_num [primalP8129]
      bound_5'' := by norm_num [primalP8129]
      triv_r := fun r => by
        cases r with
        | zero => norm_num [bluePrefix_zero, primalP8129, primalU8129]
        | succ k => norm_num [bluePrefix_primalP8129_succ, primalP8129, primalU8129]
      col_r := fun r => by
        cases r with
        | zero => norm_num [bluePrefix_zero, primalP8129, primalU8129]
        | succ k => norm_num [bluePrefix_primalP8129_succ, primalP8129, primalU8129]
      book2_r := fun r => by
        cases r with
        | zero => norm_num [bluePrefix_zero, primalP8129, primalU8129]
        | succ k => norm_num [bluePrefix_primalP8129_succ, primalP8129, primalU8129]
      book3_r := fun r => by
        cases r with
        | zero => norm_num [bluePrefix_zero, primalP8129, primalU8129]
        | succ k => norm_num [bluePrefix_primalP8129_succ, primalP8129, primalU8129] }

/-- Even the hypothetical Tuza-on-`S` bound `t ≤ 3a + 3m - b + 2 * p 0` is satisfied with
exact equality at the `81/29` primal extreme ray (`81 = 18 + 69 - 18 + 12`), proving that
strengthening `τ(S)` down to `2 ν(S)` alone cannot break `81/29`. -/
theorem primal8129_satisfies_tuza_S :
    (81 : ℚ) = 3 * 6 + 3 * 23 - 18 + 2 * primalP8129 0 := by
  norm_num [primalP8129]

/-- Exact infinite-depth LP optimality at `81/29`: global upper bound plus positive-`n` attainment. -/
theorem infinite_depth_lp_81_29_exact :
    (∀ n t a m b h_hat h0 p u,
      IsValidInfiniteHierarchyPoint8129 n t a m b h_hat h0 p u →
        t ≤ (81 / 29 : ℚ) * n) ∧
    (∃ n t a m b h_hat h0 p u,
      0 < n ∧ IsValidInfiniteHierarchyPoint8129 n t a m b h_hat h0 p u ∧
        t = (81 / 29 : ℚ) * n) :=
  ⟨fun _ _ _ _ _ _ _ _ _ h => infinite_depth_lp_81_29_upper h,
   ⟨29, 81, 6, 23, 18, 6, 0, primalP8129, primalU8129, by norm_num,
    infinite_depth_lp_81_29_attained, by norm_num⟩⟩

/-- **Primal Extreme-Ray Uniqueness**: Every feasible point of the unrelaxed infinite-depth
`81/29` LP attaining `t = (81 / 29) * n` is uniquely determined across ALL coordinates and
ALL depths `r : ℕ`, with `d = h0 = h1 = 0`, `a + m = n`, and `h_hat = u 0 = p 0 = (6/29) n`. -/
theorem infinite_depth_lp_81_29_primal_unique
    {n t a m b h_hat h0 : ℚ} {p u : ℕ → ℚ}
    (h : IsValidInfiniteHierarchyPoint8129 n t a m b h_hat h0 p u)
    (ht : t = (81 / 29 : ℚ) * n) :
    a = (6 / 29 : ℚ) * n ∧
    m = (23 / 29 : ℚ) * n ∧
    b = (18 / 29 : ℚ) * n ∧
    p 0 = (6 / 29 : ℚ) * n ∧
    h_hat = (6 / 29 : ℚ) * n ∧
    h0 = 0 ∧
    u 0 = (6 / 29 : ℚ) * n ∧
    ∀ k : ℕ, p (k + 1) = 0 ∧ u (k + 1) = 0 := by
  have hd_slack := infinite_depth_lp_81_29_upper_with_d_slack h
  have ham := h.pack_am
  have hp1_nn := h.nonneg_p 1
  have hu1_nn := h.nonneg_u 1
  have ham_eq : a + m = n := by linarith
  have hp1_eq : p 1 = 0 := by linarith
  have hu1_eq : u 1 = 0 := by linarith
  have hsplit := h.split_u0
  have h3 := h.bound_3
  have h4 := h.bound_4''
  have h5 := h.bound_5
  have h5'' := h.bound_5''
  have h6a : t ≤ 3 * a + 3 * m - b + 3 * p 0 - 2 * p 1 + u 1 - u 0 := by
    simpa [bluePrefix_zero] using h.book2_r 0
  have h6b : t ≤ 3 * a + 3 * m - b + 2 * p 0 + 3 * p 1 - u 1 := by
    have ht1 := h.triv_r 1
    rw [bluePrefix_succ, bluePrefix_zero] at ht1
    linarith
  have h3_eq : t = 3 * n - a := by linarith
  have h4_eq : t = (3 / 2 : ℚ) * n + (5 / 2 : ℚ) * a + (3 / 2 : ℚ) * b - p 0 +
      (1 / 4 : ℚ) * h_hat := by linarith
  have h5_eq : t = 3 * a + 3 * m - p 0 - p 1 := by linarith
  have h5''_eq : t = 3 * a + 3 * m - 2 * p 0 + h_hat + 2 * h0 := by linarith
  have h6b_eq : t = 3 * a + 3 * m - b + 2 * p 0 + 3 * p 1 - u 1 := by linarith
  have ha : a = (6 / 29 : ℚ) * n := by linarith
  have hm : m = (23 / 29 : ℚ) * n := by linarith
  have hp0 : p 0 = (6 / 29 : ℚ) * n := by linarith
  have hb : b = (18 / 29 : ℚ) * n := by linarith
  have hh_hat : h_hat = (6 / 29 : ℚ) * n := by linarith
  have hh0 : h0 = 0 := by linarith
  have hu0 : u 0 = (6 / 29 : ℚ) * n := by linarith
  have htail : ∀ k : ℕ, p (k + 1) = 0 ∧ u (k + 1) = 0 := by
    intro k
    induction k with
    | zero => exact ⟨hp1_eq, hu1_eq⟩
    | succ k ih =>
      have hdisj := h.disj_pu (k + 1)
      have hp_next := h.nonneg_p (k + 2)
      have hu_next := h.nonneg_u (k + 2)
      have hp_zero : p (k + 2) = 0 := by linarith [ih.1, ih.2]
      have hdisj2 := h.disj_pu (k + 2)
      have hp_next2 := h.nonneg_p (k + 3)
      have hu_zero : u (k + 2) = 0 := by linarith
      exact ⟨hp_zero, hu_zero⟩
  exact ⟨ha, hm, hb, hp0, hh_hat, hh0, hu0, htail⟩

/-- **Unique Dual Certificate Theorem**: On the 6-cover system `(3), (4''), (5), (5''), (6a), (6b)`,
any normalized multiplier vector `(y3, y4, y5, y5p, y6a, y6b)` satisfying the `a, b, c, d, h_0`
elimination inequalities and certifying `τ ≤ (81 / 29) * n` MUST equal
`(10/29, 4/29, 8/29, 1/29, 2/29, 4/29)` (which automatically satisfies non-negativity and the
remaining `h_hat` and `h_1` dual inequalities). -/
theorem dual_certificate_81_29_unique
    {y3 y4 y5 y5p y6a y6b : ℚ}
    (hsum : y3 + y4 + y5 + y5p + y6a + y6b = 1)
    (h_a : -y3 + (5 / 2 : ℚ) * y4 ≤ 0)
    (h_b : (3 / 2 : ℚ) * y4 - y6a - y6b ≤ 0)
    (h_c : -y4 - y5 - 2 * y5p + 3 * y6a + 2 * y6b ≤ 0)
    (h_d : -y5 - 2 * y6a + 3 * y6b ≤ 0)
    (h_h0 : 2 * y5p - y6a ≤ 0)
    (h_obj : 3 * y3 + (3 / 2 : ℚ) * y4 + 3 * y5 + 3 * y5p + 3 * y6a + 3 * y6b ≤ 81 / 29) :
    y3 = 10 / 29 ∧ y4 = 4 / 29 ∧ y5 = 8 / 29 ∧
      y5p = 1 / 29 ∧ y6a = 2 / 29 ∧ y6b = 4 / 29 := by
  have hy4_ge : (4 / 29 : ℚ) ≤ y4 := by linarith
  have hy3_ge : (5 / 2 : ℚ) * y4 ≤ y3 := by linarith
  have h6ab_ge : (3 / 2 : ℚ) * y4 ≤ y6a + y6b := by linarith
  have h5_plus : y5 + y5p ≤ 1 - 4 * y4 := by linarith
  have h_y6a_le : y6a ≤ y4 + y5 + 2 * y5p - 2 * (y6a + y6b) := by linarith
  have h_comb : y4 ≤ 4 / 29 := by linarith
  have hy4_eq : y4 = 4 / 29 := by linarith
  have hy3_eq : y3 = 10 / 29 := by linarith
  have h6ab_eq : y6a + y6b = 6 / 29 := by linarith
  have h5sum_eq : y5 + y5p = 9 / 29 := by linarith
  have hy6a_le1 : y6a ≤ (1 / 29 : ℚ) + y5p := by linarith
  have hy5p_le : y5p ≤ 1 / 29 := by linarith
  have hy5p_ge : 1 / 29 ≤ y5p := by linarith
  have hy5p_eq : y5p = 1 / 29 := by linarith
  have hy5_eq : y5 = 8 / 29 := by linarith
  have hy6a_eq : y6a = 2 / 29 := by linarith
  have hy6b_eq : y6b = 4 / 29 := by linarith
  exact ⟨hy3_eq, hy4_eq, hy5_eq, hy5p_eq, hy6a_eq, hy6b_eq⟩


/-! ## Section 2: Unrelaxed Graph-Level `81/29` Bounds & Exact Conditional Structural Slices -/

section ConditionalSlices

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace Construction

variable {edges : Finset (Sym2 V)} (c : Construction edges)

/-- Unrelaxed equation `(5)` retaining `3 * a + 3 * m`: `τ(G) + c + d ≤ 3 * a + 3 * m`. -/
theorem full_book_cover_unrelaxed (r : RefinedConstruction c) :
    transversalNumber (trianglesOn edges) + r.second.card + r.third.card ≤
      3 * c.first.card + 3 * c.rest.card := by
  obtain ⟨D, hD, hc⟩ := ThreeLayer.exists_third_cover r
  have hres : IsCover (residual (trianglesOn edges) (support c.first)) D := by
    rw [← trianglesOn_sdiff]
    exact hD
  have hcov : IsCover (trianglesOn edges) (support c.first ∪ D) := cover_union_residual hres
  have ht := hcov.number_le
  have hsize := c.first_packing.card_support_uniform
    (fun _ hT => trianglesOn_card (c.first_packing.1 hT))
  have hu := card_union_le (support c.first) D
  omega

/-- Unrelaxed equation `(5'')` retaining `3 * a + 3 * m`:
`τ(G) + 2 * c ≤ 3 * a + 3 * m + h_hat + 2 * h_0`. -/
theorem opposite_elimination_cover_unrelaxed (r : RefinedConstruction c) :
    transversalNumber (trianglesOn edges) + 2 * r.second.card ≤
      3 * c.first.card + 3 * c.rest.card +
        (HelperArborescence.helperRoots c r.second_maximum.1).card +
        2 * (OppositeElimination.privZeroPages c r.second_maximum.1).card := by
  let D := OppositeElimination.remainingCoreCover c r.second_maximum.1
  have hD : IsCover (trianglesOn c.remainingEdges) D :=
    OppositeElimination.remainingCoreCover_covers c r.second_maximum.1
  have hDcard : D.card + 2 * r.second.card ≤
      3 * c.rest.card + (HelperArborescence.helperRoots c r.second_maximum.1).card +
        2 * (OppositeElimination.privZeroPages c r.second_maximum.1).card :=
    OppositeElimination.remainingCoreCover_card_le c r.second_maximum.1
  have hres : IsCover (residual (trianglesOn edges) (support c.first)) D := by
    rw [← trianglesOn_sdiff]
    exact hD
  have hcov : IsCover (trianglesOn edges) (support c.first ∪ D) := cover_union_residual hres
  have ht := hcov.number_le
  have hsize := c.first_packing.card_support_uniform
    (fun _ hT => trianglesOn_card (c.first_packing.1 hT))
  have hu := card_union_le (support c.first) D
  omega

/-- Unrelaxed lifting of any cover of `c.specialFamily` retaining `3 * a + 3 * m`:
`τ(G) + b ≤ 3 * a + 3 * m + τ(S)`. -/
theorem transversalNumber_le_add_specialFamily_unrelaxed :
    transversalNumber (trianglesOn edges) + c.typeTwo.card ≤
      3 * c.first.card + 3 * c.rest.card + transversalNumber c.specialFamily := by
  obtain ⟨D, hD, hDcard⟩ := exists_minimumCover c.specialFamily
    (fun _ hT => c.specialFamily_colored.member_nonempty hT)
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
  have ht := hC.number_le
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
  omega

/-- Unrelaxed equation `(6a)`: `τ(G) + b + 2d + h ≤ 3a + 3m + 3c + h_1`. -/
theorem unmerged_cover_6a_unrelaxed (r : RefinedConstruction c) :
    transversalNumber (trianglesOn edges) + c.typeTwo.card + 2 * r.third.card +
      (privateRedPages c.specialFamily c.newEdges r.second).card ≤
    3 * c.first.card + 3 * c.rest.card + 3 * r.second.card +
      (privateRedPages (residual c.specialFamily (blueEdges c.newEdges r.second))
        c.newEdges r.third).card := by
  have hfirst : transversalNumber c.specialFamily + 2 * r.third.card +
      (privateRedPages c.specialFamily c.newEdges r.second).card ≤
    3 * r.second.card +
      (privateRedPages (residual c.specialFamily (blueEdges c.newEdges r.second))
        c.newEdges r.third).card :=
    first_colored_cover r.second_maximum r.third_maximum.1 (Subset.refl _)
  have hlift := c.transversalNumber_le_add_specialFamily_unrelaxed
  omega

/-- Unrelaxed equation `(6b)`: `τ(G) + b + h_1 ≤ 3a + 3m + 2c + 3d`. -/
theorem unmerged_cover_6b_unrelaxed (r : RefinedConstruction c) :
    transversalNumber (trianglesOn edges) + c.typeTwo.card +
      (privateRedPages (residual c.specialFamily (blueEdges c.newEdges r.second))
        c.newEdges r.third).card ≤
    3 * c.first.card + 3 * c.rest.card + 2 * r.second.card + 3 * r.third.card := by
  have hsec : transversalNumber c.specialFamily +
      (privateRedPages (residual c.specialFamily (blueEdges c.newEdges r.second))
        c.newEdges r.third).card ≤ 2 * r.second.card + 3 * r.third.card :=
    second_colored_cover c.specialFamily_colored r.second_maximum.1 r.third_maximum
  have hlift := c.transversalNumber_le_add_specialFamily_unrelaxed
  omega

/-- Unrelaxed equation `(6c)`: `3 τ(G) + 3b + 2 h_1 ≤ 9a + 9m + 6c + 8d`. -/
theorem unmerged_cover_6c_unrelaxed (r : RefinedConstruction c) :
    3 * transversalNumber (trianglesOn edges) + 3 * c.typeTwo.card +
      2 * (privateRedPages (residual c.specialFamily (blueEdges c.newEdges r.second))
        c.newEdges r.third).card ≤
    9 * c.first.card + 9 * c.rest.card + 6 * r.second.card + 8 * r.third.card := by
  have hrec : 3 * transversalNumber c.specialFamily +
      2 * (privateRedPages (residual c.specialFamily (blueEdges c.newEdges r.second))
        c.newEdges r.third).card ≤ 6 * r.second.card + 8 * r.third.card :=
    recursive_colored_cover r.second_maximum r.third_maximum
  have hlift := c.transversalNumber_le_add_specialFamily_unrelaxed
  omega

/-- Structural inequality `c ≤ b` (`|Q| ≤ |B*|`). -/
theorem second_card_le_typeTwo_card (r : RefinedConstruction c) :
    r.second.card ≤ c.typeTwo.card := by
  have hsub := OppositeElimination.pairedRest_subset_typeTwo c r.second_maximum.1
  have hcard := OppositeElimination.pairedRest_card c r.second_maximum.1
  have hle := card_le_card hsub
  omega

/-- Structural inequality `h_1 ≤ d`. -/
theorem third_priv_card_le_third_card (r : RefinedConstruction c) :
    (privateRedPages (residual c.specialFamily (blueEdges c.newEdges r.second))
      c.newEdges r.third).card ≤ r.third.card :=
  card_le_card (privateRedPages_subset _ _ _)

/-- Structural inequality `h ≤ c`. -/
theorem second_priv_card_le_second_card (r : RefinedConstruction c) :
    (privateRedPages c.specialFamily c.newEdges r.second).card ≤ r.second.card :=
  card_le_card (privateRedPages_subset _ _ _)

/-- If `c = 0` (`|Q| = 0`), then `d = 0` (`|Q_1| = 0`) because `Q` is maximum in `S`. -/
theorem third_card_eq_zero_of_second_eq_zero (r : RefinedConstruction c)
    (hc0 : r.second.card = 0) : r.third.card = 0 := by
  have hle := r.second_maximum.2 r.third (ThreeLayer.third_packing r)
  omega

/-- **Full-Slack Unrelaxed `81/29` Bound**:
`29 * τ(G) + 45 * (n - (a + m)) + 2 * h_1 ≤ 81 * n`
(proved directly on `(c, r)` with `a + m ≤ n`). -/
theorem bound_81_29_full_slack (r : RefinedConstruction c) :
    29 * transversalNumber (trianglesOn edges) +
      45 * (c.initial.card - (c.first.card + c.rest.card)) +
      2 * (privateRedPages (residual c.specialFamily (blueEdges c.newEdges r.second))
        c.newEdges r.third).card ≤
      81 * c.initial.card := by
  have ham := c.first_rest_card_le
  have hh := c.helperRoots_add_privZeroPages_card r
  have hb3 := c.first_cover
  have hb4pp := c.helper_arborescence_random_cover_unrelaxed r
  have hb5 := c.full_book_cover_unrelaxed r
  have hb5pp := c.opposite_elimination_cover_unrelaxed r
  have hb6a := c.unmerged_cover_6a_unrelaxed r
  have hb6b := c.unmerged_cover_6b_unrelaxed r
  omega

/-- **Recursive-`(6c)` Full-Slack `81/29` Bound** exposing positive slack on BOTH `d` and `h_1`:
`87 * τ(G) + 135 * (n - (a + m)) + 4 * d + 2 * h_1 ≤ 243 * n`. -/
theorem bound_81_29_with_d_slack (r : RefinedConstruction c) :
    87 * transversalNumber (trianglesOn edges) +
      135 * (c.initial.card - (c.first.card + c.rest.card)) +
      4 * r.third.card +
      2 * (privateRedPages (residual c.specialFamily (blueEdges c.newEdges r.second))
        c.newEdges r.third).card ≤
      243 * c.initial.card := by
  have ham := c.first_rest_card_le
  have hh := c.helperRoots_add_privZeroPages_card r
  have hb3 := c.first_cover
  have hb4pp := c.helper_arborescence_random_cover_unrelaxed r
  have hb5 := c.full_book_cover_unrelaxed r
  have hb5pp := c.opposite_elimination_cover_unrelaxed r
  have hb6a := c.unmerged_cover_6a_unrelaxed r
  have hb6c := c.unmerged_cover_6c_unrelaxed r
  omega

/-- **Parametrized `36/13` Private-Page Inequality** (`5*(3) + 2*(4'') + 3*(5'') + 2*(6a) + (6b)`):
`26 * τ(G) + 36 * (n - (a + m)) + 2 * (d - h_1) ≤ 72 * n + 3 * h_hat + 8 * h_0`. -/
theorem bound_36_13_parametrized (r : RefinedConstruction c) :
    26 * transversalNumber (trianglesOn edges) +
      36 * (c.initial.card - (c.first.card + c.rest.card)) +
      2 * (r.third.card -
        (privateRedPages (residual c.specialFamily (blueEdges c.newEdges r.second))
          c.newEdges r.third).card) ≤
      72 * c.initial.card +
        3 * (HelperArborescence.helperRoots c r.second_maximum.1).card +
        8 * (OppositeElimination.privZeroPages c r.second_maximum.1).card := by
  have ham := c.first_rest_card_le
  have hh := c.helperRoots_add_privZeroPages_card r
  have hd1 := c.third_priv_card_le_third_card r
  have hb3 := c.first_cover
  have hb4pp := c.helper_arborescence_random_cover_unrelaxed r
  have hb5pp := c.opposite_elimination_cover_unrelaxed r
  have hb6a := c.unmerged_cover_6a_unrelaxed r
  have hb6b := c.unmerged_cover_6b_unrelaxed r
  omega

/-- **Conditional Slice `h = 0` (`privPages = ∅`)**:
Whenever `h = 0`, `13 * τ(G) + 18 * (n - (a + m)) + (d - h_1) ≤ 36 * n`
(`τ(G) ≤ (36 / 13) * ν(G) ≈ 2.76923 * ν(G)`, beating `81/29` by `9/377`). -/
theorem bound_zero_privPages (r : RefinedConstruction c)
    (hh0 : (privateRedPages c.specialFamily c.newEdges r.second).card = 0) :
    13 * transversalNumber (trianglesOn edges) +
      18 * (c.initial.card - (c.first.card + c.rest.card)) +
      (r.third.card -
        (privateRedPages (residual c.specialFamily (blueEdges c.newEdges r.second))
          c.newEdges r.third).card) ≤
      36 * c.initial.card := by
  have hpar := c.bound_36_13_parametrized r
  have hh := c.helperRoots_add_privZeroPages_card r
  omega

/-- **Parametrized `282/101` Helper-Root Inequality**
(`35*(3) + 14*(4'') + 28*(5) + 3*(5'') + 6*(6a) + 15*(6c)`):
`202 * τ(G) + 312 * (n - (a + m)) + 8 * h_1 ≤ 564 * n + h_hat`.
Quantitatively proves that any graph exceeding `(282 / 101) * ν(G)` MUST have `h_hat > 0`. -/
theorem bound_282_101_parametrized (r : RefinedConstruction c) :
    202 * transversalNumber (trianglesOn edges) +
      312 * (c.initial.card - (c.first.card + c.rest.card)) +
      8 * (privateRedPages (residual c.specialFamily (blueEdges c.newEdges r.second))
        c.newEdges r.third).card ≤
      564 * c.initial.card +
        (HelperArborescence.helperRoots c r.second_maximum.1).card := by
  have ham := c.first_rest_card_le
  have hh := c.helperRoots_add_privZeroPages_card r
  have hb3 := c.first_cover
  have hb4pp := c.helper_arborescence_random_cover_unrelaxed r
  have hb5 := c.full_book_cover_unrelaxed r
  have hb5pp := c.opposite_elimination_cover_unrelaxed r
  have hb6a := c.unmerged_cover_6a_unrelaxed r
  have hb6c := c.unmerged_cover_6c_unrelaxed r
  omega

/-- **Conditional Slice `h_hat = 0` (`helperRoots = ∅`, zero out-of-`N` red opposite edges)**:
Whenever `h_hat = 0`, `101 * τ(G) + 156 * (n - (a + m)) + 4 * h_1 ≤ 282 * n`
(`τ(G) ≤ (282 / 101) * ν(G) ≈ 2.79208 * ν(G)`, strictly beating `81/29` by `3/2929`). -/
theorem bound_zero_helperRoots (r : RefinedConstruction c)
    (hhat0 : (HelperArborescence.helperRoots c r.second_maximum.1).card = 0) :
    101 * transversalNumber (trianglesOn edges) +
      156 * (c.initial.card - (c.first.card + c.rest.card)) +
      4 * (privateRedPages (residual c.specialFamily (blueEdges c.newEdges r.second))
        c.newEdges r.third).card ≤
      282 * c.initial.card := by
  have hpar := c.bound_282_101_parametrized r
  omega

/-- **Conditional Slice `a = 0` (`c.first = ∅`, zero type-1 triangles)**:
Whenever `a = 0`, `19 * τ(G) + 45 * (n - m) + 2 * h_1 ≤ 51 * n`
(`τ(G) ≤ (51 / 19) * ν(G) ≈ 2.68421 * ν(G)`). -/
theorem bound_zero_typeOne (r : RefinedConstruction c)
    (ha0 : c.first.card = 0) :
    19 * transversalNumber (trianglesOn edges) +
      45 * (c.initial.card - c.rest.card) +
      2 * (privateRedPages (residual c.specialFamily (blueEdges c.newEdges r.second))
        c.newEdges r.third).card ≤
      51 * c.initial.card := by
  have ham := c.first_rest_card_le
  have hh := c.helperRoots_add_privZeroPages_card r
  have hb4pp := c.helper_arborescence_random_cover_unrelaxed r
  have hb5 := c.full_book_cover_unrelaxed r
  have hb5pp := c.opposite_elimination_cover_unrelaxed r
  have hb6a := c.unmerged_cover_6a_unrelaxed r
  have hb6b := c.unmerged_cover_6b_unrelaxed r
  omega

/-- **Conditional Slice `c = 0` (`r.second = ∅`, empty residual family `S`)**:
Whenever `c = 0`, `10 * τ(G) + 9 * (n - (a + m)) ≤ 27 * n` (`τ(G) ≤ (27 / 10) * ν(G)`). -/
theorem bound_zero_second (r : RefinedConstruction c)
    (hc0 : r.second.card = 0) :
    10 * transversalNumber (trianglesOn edges) +
      9 * (c.initial.card - (c.first.card + c.rest.card)) ≤
      27 * c.initial.card := by
  have ham := c.first_rest_card_le
  have hd0 := c.third_card_eq_zero_of_second_eq_zero r hc0
  have hh1_le := c.third_priv_card_le_third_card r
  have hh_le := c.second_priv_card_le_second_card r
  have hh := c.helperRoots_add_privZeroPages_card r
  have hb3 := c.first_cover
  have hb4pp := c.helper_arborescence_random_cover_unrelaxed r
  have hb6a := c.unmerged_cover_6a_unrelaxed r
  omega

/-- **Conditional Slice `b = 0` (`c.typeTwo = ∅`, zero type-2 triangles)**:
Whenever `b = 0`, `7 * τ(G) ≤ 18 * n` (`τ(G) ≤ (18 / 7) * ν(G) ≈ 2.57143 * ν(G)`). -/
theorem bound_zero_typeTwo (r : RefinedConstruction c)
    (hb0 : c.typeTwo.card = 0) :
    7 * transversalNumber (trianglesOn edges) ≤ 18 * c.initial.card := by
  have hc_le := c.second_card_le_typeTwo_card r
  have hh_le := c.second_priv_card_le_second_card r
  have hh := c.helperRoots_add_privZeroPages_card r
  have hb3 := c.first_cover
  have hb4pp := c.helper_arborescence_random_cover_unrelaxed r
  omega

/-- **Two-Way Conditional Slice `a = 0 ∧ h = 0`**:
`8 * τ(G) + 18 * (n - m) + (d - h_1) ≤ 21 * n` (`τ(G) ≤ (21 / 8) * ν(G) = 2.625 * ν(G)`). -/
theorem bound_zero_typeOne_zero_privPages (r : RefinedConstruction c)
    (ha0 : c.first.card = 0)
    (hh0 : (privateRedPages c.specialFamily c.newEdges r.second).card = 0) :
    8 * transversalNumber (trianglesOn edges) +
      18 * (c.initial.card - c.rest.card) +
      (r.third.card -
        (privateRedPages (residual c.specialFamily (blueEdges c.newEdges r.second))
          c.newEdges r.third).card) ≤
      21 * c.initial.card := by
  have ham := c.first_rest_card_le
  have hh := c.helperRoots_add_privZeroPages_card r
  have hd1 := c.third_priv_card_le_third_card r
  have hb4pp := c.helper_arborescence_random_cover_unrelaxed r
  have hb5pp := c.opposite_elimination_cover_unrelaxed r
  have hb6a := c.unmerged_cover_6a_unrelaxed r
  have hb6b := c.unmerged_cover_6b_unrelaxed r
  omega

/-- **Two-Way Conditional Slice `d = 0 ∧ h = 0`**:
`4 * τ(G) + 5 * (n - (a + m)) ≤ 11 * n` (`τ(G) ≤ (11 / 4) * ν(G) = 2.75 * ν(G)`). -/
theorem bound_zero_third_zero_privPages (r : RefinedConstruction c)
    (hd0 : r.third.card = 0)
    (hh0 : (privateRedPages c.specialFamily c.newEdges r.second).card = 0) :
    4 * transversalNumber (trianglesOn edges) +
      5 * (c.initial.card - (c.first.card + c.rest.card)) ≤
      11 * c.initial.card := by
  have ham := c.first_rest_card_le
  have hh := c.helperRoots_add_privZeroPages_card r
  have hb3 := c.first_cover
  have hb4pp := c.helper_arborescence_random_cover_unrelaxed r
  have hb5pp := c.opposite_elimination_cover_unrelaxed r
  have hb6b := c.unmerged_cover_6b_unrelaxed r
  omega

/-- **Two-Way Conditional Slice `d = 0 ∧ h_hat = 0`**:
`14 * τ(G) + 21 * (n - (a + m)) ≤ 39 * n` (`τ(G) ≤ (39 / 14) * ν(G) ≈ 2.78571 * ν(G)`). -/
theorem bound_zero_third_zero_helperRoots (r : RefinedConstruction c)
    (hd0 : r.third.card = 0)
    (hhat0 : (HelperArborescence.helperRoots c r.second_maximum.1).card = 0) :
    14 * transversalNumber (trianglesOn edges) +
      21 * (c.initial.card - (c.first.card + c.rest.card)) ≤
      39 * c.initial.card := by
  have ham := c.first_rest_card_le
  have hb3 := c.first_cover
  have hb4pp := c.helper_arborescence_random_cover_unrelaxed r
  have hb5 := c.full_book_cover_unrelaxed r
  have hb6b := c.unmerged_cover_6b_unrelaxed r
  omega

end Construction

end ConditionalSlices


/-! ## Section 3: Disjoint-Copy Additivity and Unconditional Extremal Tightness Families -/

section DisjointCopies

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- Disjoint union of `k` isomorphic copies of a simple graph `G` on `Fin k × W`. -/
def disjointCopy (k : ℕ) (G : SimpleGraph W) : SimpleGraph (Fin k × W) where
  Adj x y := x.1 = y.1 ∧ G.Adj x.2 y.2
  symm := ⟨fun _ _ ⟨h1, h2⟩ => ⟨h1.symm, h2.symm⟩⟩
  loopless := ⟨fun x ⟨_, h2⟩ => G.loopless.irrefl x.2 h2⟩

/-- Embedding of vertex set `W` into the `i`-th copy of `Fin k × W`. -/
def copyVertEmb (k : ℕ) (i : Fin k) : W ↪ Fin k × W :=
  ⟨fun w => (i, w), fun _ _ h => (Prod.mk.inj h).2⟩

/-- Induced injection of edges `Sym2 W ↪ Sym2 (Fin k × W)` into copy `i`. -/
def copyEdgeEmb (k : ℕ) (i : Fin k) : Sym2 W ↪ Sym2 (Fin k × W) :=
  ⟨Sym2.map (copyVertEmb k i), Sym2.map.injective (copyVertEmb k i).injective⟩

/-- Induced injection of triangles into copy `i`. -/
def copyTriEmb (k : ℕ) (i : Fin k) : Finset (Sym2 W) ↪ Finset (Sym2 (Fin k × W)) :=
  (Finset.mapEmbedding (copyEdgeEmb k i)).toEmbedding

omit [Fintype W] [DecidableEq W] in
theorem copyEdgeEmb_apply (k : ℕ) (i : Fin k) (u v : W) :
    copyEdgeEmb k i s(u, v) = s((i, u), (i, v)) := rfl

omit [Fintype W] [DecidableEq W] in
@[simp] theorem copyTriEmb_apply (k : ℕ) (i : Fin k) (T : Finset (Sym2 W)) :
    copyTriEmb k i T = T.map (copyEdgeEmb k i) := rfl

omit [Fintype W] [DecidableEq W] in
theorem copyEdgeEmb_disjoint {k : ℕ} {i j : Fin k} (hij : i ≠ j)
    {e₁ e₂ : Sym2 W} : copyEdgeEmb k i e₁ ≠ copyEdgeEmb k j e₂ := by
  refine Sym2.inductionOn e₁ (fun u₁ v₁ => ?_)
  refine Sym2.inductionOn e₂ (fun u₂ v₂ => ?_)
  intro h
  simp only [copyEdgeEmb_apply, Sym2.eq_iff, Prod.mk.injEq] at h
  rcases h with ⟨⟨hi, _⟩, _⟩ | ⟨⟨hi, _⟩, _⟩ <;> exact hij hi

omit [Fintype W] in
theorem copyTriEmb_triangleEdges (k : ℕ) (i : Fin k) (u v w : W) :
    copyTriEmb k i (triangleEdges u v w) = triangleEdges (i, u) (i, v) (i, w) := by
  ext e
  simp only [copyTriEmb_apply, mem_map, mem_triangleEdges]
  constructor
  · rintro ⟨f, rfl | rfl | rfl, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  · rintro (rfl | rfl | rfl)
    · exact ⟨s(u, v), Or.inl rfl, rfl⟩
    · exact ⟨s(u, w), Or.inr (Or.inl rfl), rfl⟩
    · exact ⟨s(v, w), Or.inr (Or.inr rfl), rfl⟩

theorem copyTriEmb_mem_graphTriangles {k : ℕ} {G : SimpleGraph W} (i : Fin k)
    {T : Finset (Sym2 W)} (hT : T ∈ graphTriangles G) :
    copyTriEmb k i T ∈ graphTriangles (disjointCopy k G) := by
  obtain ⟨u, v, w, huv, huw, hvw, rfl⟩ := mem_graphTriangles_iff.mp hT
  rw [copyTriEmb_triangleEdges]
  exact mem_graphTriangles_iff.mpr
    ⟨(i, u), (i, v), (i, w), ⟨rfl, huv⟩, ⟨rfl, huw⟩, ⟨rfl, hvw⟩, rfl⟩

theorem mem_graphTriangles_disjointCopy {k : ℕ} {G : SimpleGraph W}
    {T : Finset (Sym2 (Fin k × W))} (hT : T ∈ graphTriangles (disjointCopy k G)) :
    ∃ (i : Fin k) (T' : Finset (Sym2 W)), T' ∈ graphTriangles G ∧ T = copyTriEmb k i T' := by
  obtain ⟨x, y, z, ⟨hxy1, hxy2⟩, ⟨hxz1, hxz2⟩, ⟨_, hyz2⟩, rfl⟩ := mem_graphTriangles_iff.mp hT
  refine ⟨x.1, triangleEdges x.2 y.2 z.2,
    mem_graphTriangles_iff.mpr ⟨x.2, y.2, z.2, hxy2, hxz2, hyz2, rfl⟩, ?_⟩
  rw [copyTriEmb_triangleEdges]
  have hx : (x.1, x.2) = x := rfl
  have hy : (x.1, y.2) = y := Prod.ext hxy1 rfl
  have hz : (x.1, z.2) = z := Prod.ext hxz1 rfl
  rw [hx, hy, hz]

omit [Fintype W] [DecidableEq W] in
theorem copyTriEmb_disjoint_of_ne {k : ℕ} {i j : Fin k} (hij : i ≠ j)
    (T₁ T₂ : Finset (Sym2 W)) :
    Disjoint (copyTriEmb k i T₁) (copyTriEmb k j T₂) := by
  refine disjoint_left.mpr ?_
  intro e h1 h2
  obtain ⟨e₁, _, rfl⟩ := mem_map.mp (by simpa [copyTriEmb_apply] using h1)
  obtain ⟨e₂, _, heq⟩ := mem_map.mp (by simpa [copyTriEmb_apply] using h2)
  exact copyEdgeEmb_disjoint hij heq.symm

/-- **General Additivity of `ν` under Disjoint Copies**:
`ν(k · G) = k * ν(G)` for every finite simple graph `G` and every `k : ℕ`. -/
theorem nu_disjointCopy (G : SimpleGraph W) (k : ℕ) :
    nu (disjointCopy k G) = k * nu G := by
  classical
  -- Lower bound: place a maximum packing of `G` in each of the `k` blocks
  let P₀ := maximumPacking (graphTriangles G)
  have hP₀ := (maximumPacking_spec (graphTriangles G)).1
  let P_all : Finset (Finset (Sym2 (Fin k × W))) :=
    univ.biUnion (fun i : Fin k => P₀.map (copyTriEmb k i))
  have hdisjBlocks :
      Pairwise (fun i j : Fin k =>
        Disjoint (P₀.map (copyTriEmb k i)) (P₀.map (copyTriEmb k j))) := by
    intro i j hij
    refine disjoint_left.mpr ?_
    intro T hTi hTj
    obtain ⟨T₁, hT₁, rfl⟩ := mem_map.mp hTi
    obtain ⟨T₂, _, heq⟩ := mem_map.mp hTj
    obtain ⟨e, he⟩ := trianglesOn_nonempty (hP₀.1 hT₁)
    have hm1 : copyEdgeEmb k i e ∈ copyTriEmb k i T₁ := by
      rw [copyTriEmb_apply]
      exact mem_map.mpr ⟨e, he, rfl⟩
    have hm2 : copyEdgeEmb k i e ∈ copyTriEmb k j T₂ := heq.symm ▸ hm1
    exact disjoint_left.mp (copyTriEmb_disjoint_of_ne hij T₁ T₂) hm1 hm2
  have hP_all_pack : IsPacking (graphTriangles (disjointCopy k G)) P_all := by
    refine ⟨?_, ?_⟩
    · intro T hT
      obtain ⟨i, _, hTi⟩ := mem_biUnion.mp hT
      obtain ⟨T', hT', rfl⟩ := mem_map.mp hTi
      exact copyTriEmb_mem_graphTriangles i (hP₀.1 hT')
    · intro T₁ hT₁ T₂ hT₂ hne
      obtain ⟨i, _, hT₁i⟩ := mem_biUnion.mp hT₁
      obtain ⟨j, _, hT₂j⟩ := mem_biUnion.mp hT₂
      obtain ⟨S₁, hS₁, rfl⟩ := mem_map.mp hT₁i
      obtain ⟨S₂, hS₂, rfl⟩ := mem_map.mp hT₂j
      by_cases hij : i = j
      · subst hij
        have hSne : S₁ ≠ S₂ := fun h => hne (congrArg (copyTriEmb k i) h)
        rw [copyTriEmb_apply, copyTriEmb_apply]
        exact (disjoint_map (copyEdgeEmb k i)).mpr (hP₀.2 hS₁ hS₂ hSne)
      · exact copyTriEmb_disjoint_of_ne hij S₁ S₂
  have hP_all_card : P_all.card = k * nu G := by
    rw [card_biUnion (fun i _ j _ hij => hdisjBlocks hij)]
    simp only [card_map, sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
    rfl
  have hge : k * nu G ≤ nu (disjointCopy k G) :=
    (le_nu_iff (disjointCopy k G) (k * nu G)).mpr ⟨P_all, hP_all_pack, hP_all_card.ge⟩
  -- Upper bound: project a maximum packing of `disjointCopy k G` onto each block `i`
  let P := maximumPacking (graphTriangles (disjointCopy k G))
  have hP := (maximumPacking_spec (graphTriangles (disjointCopy k G))).1
  let blockPack (i : Fin k) : Finset (Finset (Sym2 W)) :=
    (graphTriangles G).filter (fun T' => copyTriEmb k i T' ∈ P)
  have hblockPack : ∀ i : Fin k, IsPacking (graphTriangles G) (blockPack i) := by
    intro i
    refine ⟨filter_subset _ _, ?_⟩
    intro T₁ hT₁ T₂ hT₂ hne
    have h1P : copyTriEmb k i T₁ ∈ P := (mem_filter.mp hT₁).2
    have h2P : copyTriEmb k i T₂ ∈ P := (mem_filter.mp hT₂).2
    have hne' : copyTriEmb k i T₁ ≠ copyTriEmb k i T₂ :=
      fun h => hne ((copyTriEmb k i).injective h)
    have hdisj := hP.2 h1P h2P hne'
    rw [copyTriEmb_apply, copyTriEmb_apply] at hdisj
    exact (disjoint_map (copyEdgeEmb k i)).mp hdisj
  have hP_sub : P ⊆ univ.biUnion (fun i : Fin k => (blockPack i).map (copyTriEmb k i)) := by
    intro T hT
    obtain ⟨i, T', hT'G, rfl⟩ := mem_graphTriangles_disjointCopy (hP.1 hT)
    exact mem_biUnion.mpr ⟨i, mem_univ _,
      mem_map.mpr ⟨T', mem_filter.mpr ⟨hT'G, hT⟩, rfl⟩⟩
  have hle : nu (disjointCopy k G) ≤ k * nu G := by
    calc
      nu (disjointCopy k G) = P.card := rfl
      _ ≤ (univ.biUnion (fun i : Fin k => (blockPack i).map (copyTriEmb k i))).card :=
        card_le_card hP_sub
      _ ≤ ∑ i : Fin k, ((blockPack i).map (copyTriEmb k i)).card := card_biUnion_le
      _ = ∑ i : Fin k, (blockPack i).card := by simp only [card_map]
      _ ≤ ∑ _i : Fin k, nu G := sum_le_sum (fun i _ => (hblockPack i).card_le)
      _ = k * nu G := by simp
  exact Nat.le_antisymm hle hge

/-- **General Additivity of `τ` under Disjoint Copies**:
`τ(k · G) = k * τ(G)` for every finite simple graph `G` and every `k : ℕ`. -/
theorem tau_disjointCopy (G : SimpleGraph W) (k : ℕ) :
    tau (disjointCopy k G) = k * tau G := by
  classical
  -- Upper bound: lift a minimum cover of `G` into every copy `i`
  obtain ⟨C₀, _, hC₀, hC₀_card⟩ := exists_graph_minimumCover G
  let C_all : Finset (Sym2 (Fin k × W)) :=
    univ.biUnion (fun i : Fin k => C₀.map (copyEdgeEmb k i))
  have hC_all_cov : IsCover (graphTriangles (disjointCopy k G)) C_all := by
    intro T hT
    obtain ⟨i, T', hT'G, rfl⟩ := mem_graphTriangles_disjointCopy hT
    obtain ⟨e, he⟩ := hC₀ T' hT'G
    obtain ⟨heT', heC₀⟩ := mem_inter.mp he
    refine ⟨copyEdgeEmb k i e, mem_inter.mpr ⟨?_, ?_⟩⟩
    · rw [copyTriEmb_apply]
      exact mem_map.mpr ⟨e, heT', rfl⟩
    · exact mem_biUnion.mpr ⟨i, mem_univ _, mem_map.mpr ⟨e, heC₀, rfl⟩⟩
  have hle : tau (disjointCopy k G) ≤ k * tau G := by
    calc
      tau (disjointCopy k G) ≤ C_all.card := hC_all_cov.number_le
      _ ≤ ∑ i : Fin k, (C₀.map (copyEdgeEmb k i)).card := card_biUnion_le
      _ = ∑ _i : Fin k, C₀.card := by simp only [card_map]
      _ = k * tau G := by simp [hC₀_card]
  -- Lower bound: restrict a minimum cover `C` of `disjointCopy k G` to each copy `i`
  obtain ⟨C, _, hC, hC_card⟩ := exists_graph_minimumCover (disjointCopy k G)
  let blockCov (i : Fin k) : Finset (Sym2 W) :=
    (graphEdges G).filter (fun e => copyEdgeEmb k i e ∈ C)
  have hblockCov : ∀ i : Fin k, IsCover (graphTriangles G) (blockCov i) := by
    intro i T' hT'G
    obtain ⟨e, he⟩ := hC (copyTriEmb k i T') (copyTriEmb_mem_graphTriangles i hT'G)
    obtain ⟨heT, heC⟩ := mem_inter.mp he
    rw [copyTriEmb_apply] at heT
    obtain ⟨e', he'T', rfl⟩ := mem_map.mp heT
    have he'G : e' ∈ graphEdges G := (mem_trianglesOn.mp hT'G).2 he'T'
    exact ⟨e', mem_inter.mpr ⟨he'T', mem_filter.mpr ⟨he'G, heC⟩⟩⟩
  have hdisjCov :
      Pairwise (fun i j : Fin k =>
        Disjoint ((blockCov i).map (copyEdgeEmb k i)) ((blockCov j).map (copyEdgeEmb k j))) := by
    intro i j hij
    refine disjoint_left.mpr ?_
    intro e h1 h2
    obtain ⟨e₁, _, rfl⟩ := mem_map.mp h1
    obtain ⟨e₂, _, heq⟩ := mem_map.mp h2
    exact copyEdgeEmb_disjoint hij heq.symm
  have hsubC : univ.biUnion (fun i : Fin k => (blockCov i).map (copyEdgeEmb k i)) ⊆ C := by
    intro e he
    obtain ⟨i, _, hei⟩ := mem_biUnion.mp he
    obtain ⟨e', he', rfl⟩ := mem_map.mp hei
    exact (mem_filter.mp he').2
  have hge : k * tau G ≤ tau (disjointCopy k G) := by
    calc
      k * tau G = ∑ _i : Fin k, tau G := by simp
      _ ≤ ∑ i : Fin k, (blockCov i).card := sum_le_sum (fun i _ => (hblockCov i).number_le)
      _ = ∑ i : Fin k, ((blockCov i).map (copyEdgeEmb k i)).card := by simp only [card_map]
      _ = (univ.biUnion (fun i : Fin k => (blockCov i).map (copyEdgeEmb k i))).card :=
        (card_biUnion (fun i _ j _ hij => hdisjCov hij)).symm
      _ ≤ C.card := card_le_card hsubC
      _ = tau (disjointCopy k G) := hC_card
  exact Nat.le_antisymm hle hge

end DisjointCopies


/-! ### Infinite Tightness Family 1: `disjointK4 k = k · K_4` -/

/-- Disjoint union of `k` copies of `K_4`. -/
def disjointK4 (k : ℕ) : SimpleGraph (Fin k × Fin 4) :=
  disjointCopy k (⊤ : SimpleGraph (Fin 4))

/-- Exact packing number `ν(k · K_4) = k` for every `k : ℕ`. -/
theorem nu_disjointK4 (k : ℕ) : nu (disjointK4 k) = k := by
  rw [disjointK4, nu_disjointCopy, nu_complete4, mul_one]

/-- Exact transversal number `τ(k · K_4) = 2 * k` for every `k : ℕ`. -/
theorem tau_disjointK4 (k : ℕ) : tau (disjointK4 k) = 2 * k := by
  rw [disjointK4, tau_disjointCopy, tau_complete4, mul_comm]

/-- Full infinite Tuza sharpness family: `τ(k · K_4) = 2 * ν(k · K_4)` for EVERY `k : ℕ`. -/
theorem tuza_tight_disjointK4 (k : ℕ) :
    tau (disjointK4 k) = 2 * nu (disjointK4 k) := by
  rw [nu_disjointK4, tau_disjointK4]


/-! ### Classic Tightness Witness `K_5` and Infinite Family `disjointK5 k = k · K_5` -/

/-- The complete graph `K_5` has exactly `10` edges. -/
theorem complete5_edge_card : (graphEdges (⊤ : SimpleGraph (Fin 5))).card = 10 := by
  classical
  have heq : graphEdges (⊤ : SimpleGraph (Fin 5)) =
      (univ : Finset (Sym2 (Fin 5))).filter (fun e => ¬ e.IsDiag) := by
    ext e
    simp only [mem_graphEdges, mem_filter, mem_univ, true_and]
    refine Sym2.inductionOn e (fun u v => ?_)
    simp
  rw [heq]
  decide

private theorem triangleEdges_deg_even {u v w x : Fin 5}
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    Even ((triangleEdges u v w).filter (fun e => x ∈ e)).card := by
  have hcard : ((triangleEdges u v w).filter (fun e => x ∈ e)).card =
      if x = u ∨ x = v ∨ x = w then 2 else 0 := by
    have he1 : s(u, v) ≠ s(u, w) := by
      intro h; exact hvw (Sym2.congr_right.mp h)
    have he2 : s(u, v) ≠ s(v, w) := by
      intro h; rw [Sym2.eq_swap] at h; exact huw (Sym2.congr_right.mp h)
    have he3 : s(u, w) ≠ s(v, w) := by
      intro h; rw [Sym2.eq_swap, Sym2.eq_swap (a := v)] at h
      exact huv (Sym2.congr_right.mp h)
    by_cases hxu : x = u
    · subst hxu
      have hfilt : (triangleEdges x v w).filter (fun e => x ∈ e) = {s(x, v), s(x, w)} := by
        ext e
        simp only [mem_filter, mem_triangleEdges, mem_insert, mem_singleton]
        constructor
        · rintro ⟨rfl | rfl | rfl, hm⟩
          · exact Or.inl rfl
          · exact Or.inr rfl
          · simp [Sym2.mem_iff, huv, huw] at hm
        · rintro (rfl | rfl)
          · exact ⟨Or.inl rfl, by simp⟩
          · exact ⟨Or.inr (Or.inl rfl), by simp⟩
      rw [hfilt, card_pair he1]
      simp
    · by_cases hxv : x = v
      · subst hxv
        have hfilt : (triangleEdges u x w).filter (fun e => x ∈ e) = {s(u, x), s(x, w)} := by
          ext e
          simp only [mem_filter, mem_triangleEdges, mem_insert, mem_singleton]
          constructor
          · rintro ⟨rfl | rfl | rfl, hm⟩
            · exact Or.inl rfl
            · simp [Sym2.mem_iff, huv.symm, hvw] at hm
            · exact Or.inr rfl
          · rintro (rfl | rfl)
            · exact ⟨Or.inl rfl, by simp⟩
            · exact ⟨Or.inr (Or.inr rfl), by simp⟩
        rw [hfilt, card_pair he2]
        simp
      · by_cases hxw : x = w
        · subst hxw
          have hfilt : (triangleEdges u v x).filter (fun e => x ∈ e) = {s(u, x), s(v, x)} := by
            ext e
            simp only [mem_filter, mem_triangleEdges, mem_insert, mem_singleton]
            constructor
            · rintro ⟨rfl | rfl | rfl, hm⟩
              · simp [Sym2.mem_iff, huw.symm, hvw.symm] at hm
              · exact Or.inl rfl
              · exact Or.inr rfl
            · rintro (rfl | rfl)
              · exact ⟨Or.inr (Or.inl rfl), by simp⟩
              · exact ⟨Or.inr (Or.inr rfl), by simp⟩
          rw [hfilt, card_pair he3]
          simp
        · have hfilt : (triangleEdges u v w).filter (fun e => x ∈ e) = ∅ := by
            ext e
            simp only [mem_filter, mem_triangleEdges, notMem_empty, iff_false, not_and]
            rintro (rfl | rfl | rfl) hm <;>
              simp [Sym2.mem_iff, hxu, hxv, hxw] at hm
          rw [hfilt]
          simp [hxu, hxv, hxw]
  rw [hcard]
  split_ifs
  · exact ⟨1, rfl⟩
  · exact ⟨0, rfl⟩

/-- Exact packing number `ν(K_5) = 2` (proved via vertex-degree parity of `K_5 \ support P`). -/
theorem nu_complete5 : nu (⊤ : SimpleGraph (Fin 5)) = 2 := by
  classical
  let K5 : SimpleGraph (Fin 5) := ⊤
  let T₁ : Finset (Sym2 (Fin 5)) := triangleEdges 0 1 2
  let T₂ : Finset (Sym2 (Fin 5)) := triangleEdges 0 3 4
  have hT₁ : T₁ ∈ graphTriangles K5 :=
    mem_graphTriangles_iff.mpr ⟨0, 1, 2, by decide, by decide, by decide, rfl⟩
  have hT₂ : T₂ ∈ graphTriangles K5 :=
    mem_graphTriangles_iff.mpr ⟨0, 3, 4, by decide, by decide, by decide, rfl⟩
  have hd12 : Disjoint T₁ T₂ := by decide
  have hne12 : T₁ ≠ T₂ := by decide
  have hpack2 : IsPacking (graphTriangles K5) {T₁, T₂} := by
    refine ⟨insert_subset hT₁ (singleton_subset_iff.mpr hT₂), ?_⟩
    intro A hA B hB hne
    simp only [mem_coe, mem_insert, mem_singleton] at hA hB
    rcases hA with rfl | rfl <;> rcases hB with rfl | rfl
    · exact (hne rfl).elim
    · exact hd12
    · exact hd12.symm
    · exact (hne rfl).elim
  have hge : 2 ≤ nu K5 :=
    (le_nu_iff K5 2).mpr ⟨{T₁, T₂}, hpack2, by rw [card_pair hne12]⟩
  -- Upper bound: `nu K5 ≤ 2` via degree parity of `K_5 \ support P`
  let P := maximumPacking (graphTriangles K5)
  have hP := (maximumPacking_spec (graphTriangles K5)).1
  have hSsub : support P ⊆ graphEdges K5 := by
    intro e he
    obtain ⟨T, hT, heT⟩ := mem_support.mp he
    exact (mem_trianglesOn.mp (hP.1 hT)).2 heT
  have hScard : (support P).card = 3 * P.card :=
    hP.card_support_uniform (fun T hT => trianglesOn_card (hP.1 hT))
  have hEcard : (graphEdges K5).card = 10 := complete5_edge_card
  have hPle3 : P.card ≤ 3 := by
    have hle := card_le_card hSsub
    omega
  have hPne3 : P.card ≠ 3 := by
    intro hP3
    let R := graphEdges K5 \ support P
    have hRcard : R.card = 1 := by
      have hsp := card_sdiff_add_card_eq_card hSsub
      change R.card + (support P).card = (graphEdges K5).card at hsp
      omega
    obtain ⟨e₀, he₀⟩ := card_eq_one.mp hRcard
    have he₀_mem : e₀ ∈ graphEdges K5 := (mem_sdiff.mp (he₀ ▸ mem_singleton_self e₀)).1
    revert he₀ he₀_mem
    refine Sym2.inductionOn e₀ (fun a b he₀ he₀_mem => ?_)
    have hab : a ≠ b := by
      have hadj : K5.Adj a b := pair_mem_graphEdges.mp he₀_mem
      exact hadj.ne
    -- Degree of `a` in `graphEdges K5` is `4` (even)
    have hdegK5 : ((graphEdges K5).filter (fun e => a ∈ e)).card = 4 := by
      have heq : (graphEdges K5).filter (fun e => a ∈ e) =
          ((univ : Finset (Fin 5)).erase a).image (fun y => s(a, y)) := by
        ext e
        refine Sym2.inductionOn e (fun u v => ?_)
        simp only [mem_filter, pair_mem_graphEdges, Sym2.mem_iff,
          mem_image, mem_erase, mem_univ, and_true, Sym2.eq_iff]
        constructor
        · rintro ⟨huv, rfl | rfl⟩
          · exact ⟨v, huv.symm, Or.inl ⟨rfl, rfl⟩⟩
          · exact ⟨u, huv, Or.inr ⟨rfl, rfl⟩⟩
        · rintro ⟨y, hya, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
          · exact ⟨hya.symm, Or.inl rfl⟩
          · exact ⟨hya, Or.inr rfl⟩
      rw [heq, card_image_of_injective _ (fun _ _ h => Sym2.congr_right.mp h)]
      simp
    -- Degree of `a` in `support P` is even (sum of even degrees over disjoint triangles)
    have hdegS_even : Even ((support P).filter (fun e => a ∈ e)).card := by
      have hfilt_eq : (support P).filter (fun e => a ∈ e) =
          P.biUnion (fun T => T.filter (fun e => a ∈ e)) := by
        ext e
        simp only [mem_filter, mem_support, mem_biUnion]
        constructor
        · rintro ⟨⟨T, hT, heT⟩, ha⟩
          exact ⟨T, hT, heT, ha⟩
        · rintro ⟨T, hT, heT, ha⟩
          exact ⟨⟨T, hT, heT⟩, ha⟩
      rw [hfilt_eq, card_biUnion]
      · refine Finset.even_sum _ (fun T hT => ?_)
        obtain ⟨u, v, w, huv, huw, hvw, rfl⟩ := mem_graphTriangles_iff.mp (hP.1 hT)
        exact triangleEdges_deg_even huv.ne huw.ne hvw.ne
      · intro T₁ hT₁ T₂ hT₂ hne
        exact (hP.2 hT₁ hT₂ hne).mono (filter_subset _ _) (filter_subset _ _)
    -- Degree of `a` in `R = {s(a, b)}` is `1` (odd)
    have hdegR : (R.filter (fun e => a ∈ e)).card = 1 := by
      rw [he₀]
      have hfa : ({s(a, b)} : Finset (Sym2 (Fin 5))).filter (fun e => a ∈ e) = {s(a, b)} := by
        ext e; simp only [mem_filter, mem_singleton, and_iff_left_iff_imp]; rintro rfl; simp
      rw [hfa, card_singleton]
    -- Contradiction: `deg(K_5, a) = deg(R, a) + deg(support P, a)` gives `4 = 1 + 2k`
    have hdisjRS : Disjoint (R.filter (fun e => a ∈ e)) ((support P).filter (fun e => a ∈ e)) :=
      sdiff_disjoint.mono (filter_subset _ _) (filter_subset _ _)
    have hunionRS : R.filter (fun e => a ∈ e) ∪ (support P).filter (fun e => a ∈ e) =
        (graphEdges K5).filter (fun e => a ∈ e) := by
      rw [← filter_union, sdiff_union_of_subset hSsub]
    have hsum := card_union_of_disjoint hdisjRS
    rw [hunionRS, hdegK5, hdegR] at hsum
    obtain ⟨k, hk⟩ := hdegS_even
    omega
  have hle : nu K5 ≤ 2 := by
    change P.card ≤ 2
    omega
  exact Nat.le_antisymm hle hge

/-- **Mantel's Theorem for `n = 5`**: Every triangle-free edge set `H ⊆ E(K_5)` has at most `6`
edges (proved cleanly via Cauchy–Schwarz on vertex degrees). -/
theorem mantel_five {H : Finset (Sym2 (Fin 5))}
    (hsub : H ⊆ graphEdges (⊤ : SimpleGraph (Fin 5)))
    (htf : ∀ u v w : Fin 5, s(u, v) ∈ H → s(u, w) ∈ H → s(v, w) ∈ H → False) :
    H.card ≤ 6 := by
  classical
  let deg (x : Fin 5) : ℕ := (H.filter (fun e => x ∈ e)).card
  have hnoDiag : ∀ e ∈ H, ¬ e.IsDiag := by
    intro e he
    have heG := hsub he
    refine Sym2.inductionOn e (fun u v => ?_) heG
    intro hadj
    exact (pair_mem_graphEdges.mp hadj).ne
  -- Handshaking: `∑ x : Fin 5, deg x = 2 * H.card`
  have hshake : ∑ x : Fin 5, deg x = 2 * H.card := by
    calc
      ∑ x : Fin 5, deg x = ∑ x : Fin 5, ∑ e ∈ H, if x ∈ e then 1 else 0 := by
        refine sum_congr rfl (fun x _ => ?_)
        exact Finset.card_filter _ _
      _ = ∑ e ∈ H, ∑ x : Fin 5, if x ∈ e then 1 else 0 := sum_comm
      _ = ∑ _e ∈ H, 2 := by
        refine sum_congr rfl (fun e he => ?_)
        have hnd := hnoDiag e he
        revert hnd
        refine Sym2.inductionOn e (fun u v huv => ?_)
        have hne : u ≠ v := huv
        have hfilt : (univ : Finset (Fin 5)).filter (fun x => x ∈ s(u, v)) = {u, v} := by
          ext x
          simp [Sym2.mem_iff]
        rw [← card_filter, hfilt, card_pair hne]
      _ = 2 * H.card := by simp [Nat.mul_comm]
  -- For every edge `s(u, v) ∈ H`, `deg u + deg v ≤ 5` (triangle-freeness makes neighborhoods disjoint)
  have hedge_deg : ∀ e ∈ H, (∑ x : Fin 5, if x ∈ e then deg x else 0) ≤ 5 := by
    intro e he
    have hnd := hnoDiag e he
    revert he hnd
    refine Sym2.inductionOn e (fun u v he huv => ?_)
    have hne : u ≠ v := huv
    have hsum_uv : (∑ x : Fin 5, if x ∈ s(u, v) then deg x else 0) = deg u + deg v := by
      have hfilt : (univ : Finset (Fin 5)).filter (fun x => x ∈ s(u, v)) = {u, v} := by
        ext x; simp [Sym2.mem_iff]
      rw [← sum_filter, hfilt, sum_pair hne]
    rw [hsum_uv]
    let Nu : Finset (Fin 5) := univ.filter (fun w => s(u, w) ∈ H)
    let Nv : Finset (Fin 5) := univ.filter (fun w => s(v, w) ∈ H)
    have hNu_card : deg u = Nu.card := by
      have himg : Nu.image (fun w => s(u, w)) = H.filter (fun f => u ∈ f) := by
        ext f
        refine Sym2.inductionOn f (fun a b => ?_)
        simp only [mem_image, mem_filter, mem_univ, true_and, Nu, Sym2.mem_iff, Sym2.eq_iff]
        constructor
        · rintro ⟨w, hw, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
          · exact ⟨hw, Or.inl rfl⟩
          · exact ⟨by simpa [Sym2.eq_swap] using hw, Or.inr rfl⟩
        · rintro ⟨hf, rfl | rfl⟩
          · exact ⟨b, hf, Or.inl ⟨rfl, rfl⟩⟩
          · exact ⟨a, by simpa [Sym2.eq_swap] using hf, Or.inr ⟨rfl, rfl⟩⟩
      rw [← card_image_of_injective Nu (fun _ _ h => Sym2.congr_right.mp h), himg]
    have hNv_card : deg v = Nv.card := by
      have himg : Nv.image (fun w => s(v, w)) = H.filter (fun f => v ∈ f) := by
        ext f
        refine Sym2.inductionOn f (fun a b => ?_)
        simp only [mem_image, mem_filter, mem_univ, true_and, Nv, Sym2.mem_iff, Sym2.eq_iff]
        constructor
        · rintro ⟨w, hw, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
          · exact ⟨hw, Or.inl rfl⟩
          · exact ⟨by simpa [Sym2.eq_swap] using hw, Or.inr rfl⟩
        · rintro ⟨hf, rfl | rfl⟩
          · exact ⟨b, hf, Or.inl ⟨rfl, rfl⟩⟩
          · exact ⟨a, by simpa [Sym2.eq_swap] using hf, Or.inr ⟨rfl, rfl⟩⟩
      rw [← card_image_of_injective Nv (fun _ _ h => Sym2.congr_right.mp h), himg]
    have hdisj : Disjoint Nu Nv := by
      refine disjoint_left.mpr ?_
      intro w hwu hwv
      exact htf u v w he (mem_filter.mp hwu).2 (mem_filter.mp hwv).2
    rw [hNu_card, hNv_card, ← card_union_of_disjoint hdisj]
    exact (card_le_univ _).trans_eq (by decide)
  -- Sum of squared degrees ≤ `5 * H.card`
  have hsq : ∑ x : Fin 5, deg x * deg x ≤ 5 * H.card := by
    calc
      ∑ x : Fin 5, deg x * deg x =
          ∑ x : Fin 5, ∑ e ∈ H, if x ∈ e then deg x else 0 := by
        refine sum_congr rfl (fun x _ => ?_)
        rw [← sum_filter]
        simp [deg]
      _ = ∑ e ∈ H, ∑ x : Fin 5, if x ∈ e then deg x else 0 := sum_comm
      _ ≤ ∑ _e ∈ H, 5 := sum_le_sum hedge_deg
      _ = 5 * H.card := by simp [Nat.mul_comm]
  -- Cauchy–Schwarz on `Fin 5`: `(∑ deg x)^2 ≤ 5 * ∑ (deg x)^2`
  have hcs : (∑ x : Fin 5, deg x) ^ 2 ≤ 5 * ∑ x : Fin 5, deg x * deg x := by
    rw [Fin.sum_univ_five, Fin.sum_univ_five]
    zify
    nlinarith [sq_nonneg ((deg 0 : ℤ) - deg 1), sq_nonneg ((deg 0 : ℤ) - deg 2),
      sq_nonneg ((deg 0 : ℤ) - deg 3), sq_nonneg ((deg 0 : ℤ) - deg 4),
      sq_nonneg ((deg 1 : ℤ) - deg 2), sq_nonneg ((deg 1 : ℤ) - deg 3),
      sq_nonneg ((deg 1 : ℤ) - deg 4), sq_nonneg ((deg 2 : ℤ) - deg 3),
      sq_nonneg ((deg 2 : ℤ) - deg 4), sq_nonneg ((deg 3 : ℤ) - deg 4)]
  rw [hshake] at hcs
  have hquad : (2 * H.card) ^ 2 ≤ 5 * (5 * H.card) := hcs.trans (Nat.mul_le_mul_left 5 hsq)
  nlinarith

/-- Exact transversal number `τ(K_5) = 4` (attaining Tuza's `τ = 2ν` at `ν = 2`). -/
theorem tau_complete5 : tau (⊤ : SimpleGraph (Fin 5)) = 4 := by
  classical
  let K5 : SimpleGraph (Fin 5) := ⊤
  let C₀ : Finset (Sym2 (Fin 5)) := {s(0, 1), s(2, 3), s(2, 4), s(3, 4)}
  have hcov_dec : ∀ u v w : Fin 5, u ≠ v → u ≠ w → v ≠ w →
      (s(u, v) = s(0, 1) ∨ s(u, v) = s(2, 3) ∨ s(u, v) = s(2, 4) ∨ s(u, v) = s(3, 4)) ∨
      (s(u, w) = s(0, 1) ∨ s(u, w) = s(2, 3) ∨ s(u, w) = s(2, 4) ∨ s(u, w) = s(3, 4)) ∨
      (s(v, w) = s(0, 1) ∨ s(v, w) = s(2, 3) ∨ s(v, w) = s(2, 4) ∨ s(v, w) = s(3, 4)) := by
    decide
  have hC₀_cov : IsCover (graphTriangles K5) C₀ := by
    apply (graph_cover_iff_adj K5 C₀).mpr
    intro u v w huv huw hvw
    rcases hcov_dec u v w huv.ne huw.ne hvw.ne with h | h | h
    · exact Or.inl (by simpa [C₀] using h)
    · exact Or.inr (Or.inl (by simpa [C₀] using h))
    · exact Or.inr (Or.inr (by simpa [C₀] using h))
  have hle : tau K5 ≤ 4 := hC₀_cov.number_le.trans (by decide : C₀.card ≤ 4)
  -- Lower bound via Mantel's theorem on `H = E(K_5) \ C`
  obtain ⟨C, hCsub, hC, hCcard⟩ := exists_graph_minimumCover K5
  let H := graphEdges K5 \ C
  have hHtf : ∀ u v w : Fin 5, s(u, v) ∈ H → s(u, w) ∈ H → s(v, w) ∈ H → False := by
    intro u v w huv huw hvw
    have huvG : K5.Adj u v := pair_mem_graphEdges.mp (mem_sdiff.mp huv).1
    have huwG : K5.Adj u w := pair_mem_graphEdges.mp (mem_sdiff.mp huw).1
    have hvwG : K5.Adj v w := pair_mem_graphEdges.mp (mem_sdiff.mp hvw).1
    rcases (graph_cover_iff_adj K5 C).mp hC u v w huvG huwG hvwG with h1 | h2 | h3
    · exact (mem_sdiff.mp huv).2 h1
    · exact (mem_sdiff.mp huw).2 h2
    · exact (mem_sdiff.mp hvw).2 h3
  have hHle : H.card ≤ 6 := mantel_five sdiff_subset hHtf
  have hsplit := card_sdiff_add_card_eq_card hCsub
  have hE10 : (graphEdges K5).card = 10 := complete5_edge_card
  have hge : 4 ≤ tau K5 := by
    change H.card + C.card = (graphEdges K5).card at hsplit
    omega
  exact Nat.le_antisymm hle hge

/-- Classic Tuza sharpness witness `K_5`: `τ(K_5) = 2 * ν(K_5)`. -/
theorem tuza_tight_complete5 :
    tau (⊤ : SimpleGraph (Fin 5)) = 2 * nu (⊤ : SimpleGraph (Fin 5)) := by
  rw [nu_complete5, tau_complete5]

/-- Disjoint union of `k` copies of `K_5`. -/
def disjointK5 (k : ℕ) : SimpleGraph (Fin k × Fin 5) :=
  disjointCopy k (⊤ : SimpleGraph (Fin 5))

/-- Exact packing number `ν(k · K_5) = 2 * k` for every `k : ℕ`. -/
theorem nu_disjointK5 (k : ℕ) : nu (disjointK5 k) = 2 * k := by
  rw [disjointK5, nu_disjointCopy, nu_complete5, mul_comm]

/-- Exact transversal number `τ(k · K_5) = 4 * k` for every `k : ℕ`. -/
theorem tau_disjointK5 (k : ℕ) : tau (disjointK5 k) = 4 * k := by
  rw [disjointK5, tau_disjointCopy, tau_complete5, mul_comm]

/-- Second infinite Tuza sharpness family: `τ(k · K_5) = 2 * ν(k · K_5)` for EVERY `k : ℕ`. -/
theorem tuza_tight_disjointK5 (k : ℕ) :
    tau (disjointK5 k) = 2 * nu (disjointK5 k) := by
  rw [nu_disjointK5, tau_disjointK5]
  ring

end TuzaBound
