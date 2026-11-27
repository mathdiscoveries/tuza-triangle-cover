/-
Copyright (c) 2026 Tyler B. Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Infinite-depth LP fixed-point recurrence (Theorem 2(a)) for `TuzaBound`.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Interval
public import Mathlib.Tactic

/-!
# Theorem 2(a): Algebraic `(8/3, 2/3)` Fixed-Point Recurrence and Infinite-Depth LP Invariance

Formalizes the algebraic mechanism explaining why adding arbitrarily many residual Lemma 2.3
packing layers `Q_2, Q_3, ..., Q_K` (`K ≥ 1`) leaves the linear-programming upper bound locked at
`699 / 250 = 2.796` (`m1-report.md` §3.2, strictly scoped to the LP hierarchy):

1. **2-Page Dominance over 3-Page Books (`book2_le_book3`)**:
   Whenever `p_{r+2} + u_{r+1} ≤ p_{r+1}`, the 2-page book bound `3 p_r - 2 p_{r+1} + u_{r+1} - u_r`
   is at most the 3-page book bound `3 p_r - p_{r+1} - p_{r+2} - u_r`.
2. **Exact `(8/3, 2/3)` Fixed-Point Recurrence (`fixed_point_recurrence`)**:
   At convex weight `λ = 1/3`, combining the depth-`r` 2-page book bound with `2 p_r` plus the
   depth-`(r+1)` `(8/3, 2/3)` bound reproduces `(8/3) p_r - (2/3) u_r - (4/9)(p_{r+1} - u_{r+1}) ≤
   (8/3) p_r - (2/3) u_r` whenever `u_{r+1} ≤ p_{r+1}`.
3. **Global Infinite-Depth LP Exactness (`infinite_depth_lp_exact_699_250`)**:
   Every feasible point `(n, t, a, m, b, p, u)` satisfying `(3)`, `(4')`, `(5)`, and all four
   Lemma 2.3 bounds at every depth `r : ℕ` obeys `t ≤ (699 / 250) * n`, and the explicit ray
   `(250, 699, 51, 199, 159, (42, 9, 3, 0, ...), (0, 0, 3, 0, ...))` satisfies the entire
   infinite-depth constraint system simultaneously with `t = (699 / 250) * n`.
-/

@[expose] public section

namespace TuzaBound

open Finset
open scoped BigOperators

/-- Disjointness `p_{r+2} + u_{r+1} ≤ p_{r+1}` makes the 2-page book bound at least as tight as
the 3-page book bound at every depth `r`. -/
theorem book2_le_book3 {pr p1 p2 ur u1 : ℚ} (hdisj : p2 + u1 ≤ p1) :
    3 * pr - 2 * p1 + u1 - ur ≤ 3 * pr - p1 - p2 - ur := by
  linarith

/-- Exact algebraic identity at `(γ, δ) = (8/3, 2/3)` and convex weight `λ = 1/3`. -/
theorem fixed_point_recurrence_eq (p q r u : ℚ) :
    (2 / 3 : ℚ) * (3 * p - 2 * q + r - u) +
      (1 / 3 : ℚ) * (2 * p + (8 / 3 : ℚ) * q - (2 / 3 : ℚ) * r) =
    (8 / 3 : ℚ) * p - (2 / 3 : ℚ) * u - (4 / 9 : ℚ) * (q - r) := by
  ring

/-- Theorem 2(a) fixed-point inequality: `(8/3, 2/3)` reproduces itself across arbitrary
depth under `r ≤ q` (`u_{k+1} ≤ p_{k+1}`). -/
theorem fixed_point_recurrence {p q r u : ℚ} (hrq : r ≤ q) :
    (2 / 3 : ℚ) * (3 * p - 2 * q + r - u) +
      (1 / 3 : ℚ) * (2 * p + (8 / 3 : ℚ) * q - (2 / 3 : ℚ) * r) ≤
    (8 / 3 : ℚ) * p - (2 / 3 : ℚ) * u := by
  have hid := fixed_point_recurrence_eq p q r u
  linarith

/-- Cumulative blue-edge prefix `∑_{j < r} 2 * p_j` deleted prior to depth `r` on `S`. -/
def bluePrefix (p : ℕ → ℚ) (r : ℕ) : ℚ :=
  ∑ j ∈ range r, 2 * p j

@[simp] theorem bluePrefix_zero (p : ℕ → ℚ) : bluePrefix p 0 = 0 := by
  simp [bluePrefix]

theorem bluePrefix_succ (p : ℕ → ℚ) (r : ℕ) :
    bluePrefix p (r + 1) = bluePrefix p r + 2 * p r := by
  simp [bluePrefix, sum_range_succ]

/-- Full infinite-depth LP constraint set combining `(3)`, `(4')`, `(5)`, packing/disjointness
constraints, and all four Lemma 2.3 bounds at every depth `r : ℕ`. -/
structure IsValidInfiniteHierarchyPoint
    (n t a m b : ℚ) (p u : ℕ → ℚ) : Prop where
  nonneg_n : 0 ≤ n
  nonneg_t : 0 ≤ t
  nonneg_a : 0 ≤ a
  nonneg_m : 0 ≤ m
  nonneg_b : 0 ≤ b
  nonneg_p : ∀ r, 0 ≤ p r
  nonneg_u : ∀ r, 0 ≤ u r
  pack_am : a + m ≤ n
  pack_bm : b ≤ m
  pack_p0 : p 0 ≤ b
  disj_pu : ∀ r, p (r + 1) + u r ≤ p r
  bound_3 : t ≤ 3 * n - a
  bound_4' : t ≤ (3 / 2 : ℚ) * n + (5 / 2 : ℚ) * a + (3 / 2 : ℚ) * b - p 0 + (1 / 4 : ℚ) * u 0
  bound_5 : t ≤ 3 * a + 3 * m - p 0 - p 1
  triv_r : ∀ r, t ≤ 3 * a + 3 * m - b + bluePrefix p r + 3 * p r - u r
  col_r : ∀ r, t ≤ 3 * a + 3 * m - b + bluePrefix p r + (8 / 3 : ℚ) * p r - (2 / 3 : ℚ) * u r
  book2_r : ∀ r, t ≤ 3 * a + 3 * m - b + bluePrefix p r + 3 * p r - 2 * p (r + 1) + u (r + 1) - u r
  book3_r : ∀ r, t ≤ 3 * a + 3 * m - b + bluePrefix p r + 3 * p r - p (r + 1) - p (r + 2) - u r

/-- Upper bound for the infinite-depth LP relaxation: every feasible point obeys `t ≤ (699/250) n`. -/
theorem infinite_depth_lp_upper {n t a m b : ℚ} {p u : ℕ → ℚ}
    (h : IsValidInfiniteHierarchyPoint n t a m b p u) :
    t ≤ (699 / 250 : ℚ) * n := by
  have ham := h.pack_am
  have hu0 := h.nonneg_u 0
  have hu1 := h.nonneg_u 1
  have h3 := h.bound_3
  have h4 := h.bound_4'
  have h5 := h.bound_5
  have h6a : t ≤ 3 * a + 3 * m - b + 3 * p 0 - 2 * p 1 + u 1 - u 0 := by
    simpa [bluePrefix_zero] using h.book2_r 0
  have h6c : t ≤ 3 * a + 3 * m - b + 2 * p 0 + (8 / 3 : ℚ) * p 1 - (2 / 3 : ℚ) * u 1 := by
    have hc1 := h.col_r 1
    rw [bluePrefix_succ, bluePrefix_zero] at hc1
    linarith
  linarith

/-- Primal packing sequence `(42, 9, 3, 0, 0, ...)` at `n = 250`. -/
def primalP : ℕ → ℚ
  | 0 => 42
  | 1 => 9
  | 2 => 3
  | _ + 3 => 0

/-- Primal private-spine sequence `(0, 0, 3, 0, 0, ...)` at `n = 250`. -/
def primalU : ℕ → ℚ
  | 0 => 0
  | 1 => 0
  | 2 => 3
  | _ + 3 => 0

theorem bluePrefix_primalP_one : bluePrefix primalP 1 = 84 := by
  rw [bluePrefix_succ, bluePrefix_zero, primalP]
  norm_num

theorem bluePrefix_primalP_two : bluePrefix primalP 2 = 102 := by
  rw [bluePrefix_succ, bluePrefix_primalP_one, primalP]
  norm_num

theorem bluePrefix_primalP_add_three (k : ℕ) : bluePrefix primalP (k + 3) = 108 := by
  induction k with
  | zero =>
    rw [bluePrefix_succ, bluePrefix_primalP_two, primalP]
    norm_num
  | succ k ih =>
    have hstep : bluePrefix primalP (k + 4) = bluePrefix primalP (k + 3) + 2 * primalP (k + 3) :=
      bluePrefix_succ primalP (k + 3)
    rw [hstep, ih, primalP]
    norm_num

/-- Exact primal feasibility of `(n = 250, t = 699)` across ALL depths `r : ℕ` simultaneously. -/
theorem infinite_depth_lp_attained :
    IsValidInfiniteHierarchyPoint 250 699 51 199 159 primalP primalU := by
  refine
    { nonneg_n := by norm_num
      nonneg_t := by norm_num
      nonneg_a := by norm_num
      nonneg_m := by norm_num
      nonneg_b := by norm_num
      nonneg_p := fun r => by match r with | 0 | 1 | 2 | _ + 3 => norm_num [primalP]
      nonneg_u := fun r => by match r with | 0 | 1 | 2 | _ + 3 => norm_num [primalU]
      pack_am := by norm_num
      pack_bm := by norm_num
      pack_p0 := by norm_num [primalP]
      disj_pu := fun r => by match r with | 0 | 1 | 2 | _ + 3 => norm_num [primalP, primalU]
      bound_3 := by norm_num
      bound_4' := by norm_num [primalP, primalU]
      bound_5 := by norm_num [primalP]
      triv_r := fun r => by
        match r with
        | 0 => norm_num [bluePrefix_zero, primalP, primalU]
        | 1 => norm_num [bluePrefix_primalP_one, primalP, primalU]
        | 2 => norm_num [bluePrefix_primalP_two, primalP, primalU]
        | k + 3 => norm_num [bluePrefix_primalP_add_three, primalP, primalU]
      col_r := fun r => by
        match r with
        | 0 => norm_num [bluePrefix_zero, primalP, primalU]
        | 1 => norm_num [bluePrefix_primalP_one, primalP, primalU]
        | 2 => norm_num [bluePrefix_primalP_two, primalP, primalU]
        | k + 3 => norm_num [bluePrefix_primalP_add_three, primalP, primalU]
      book2_r := fun r => by
        match r with
        | 0 => norm_num [bluePrefix_zero, primalP, primalU]
        | 1 => norm_num [bluePrefix_primalP_one, primalP, primalU]
        | 2 => norm_num [bluePrefix_primalP_two, primalP, primalU]
        | k + 3 => norm_num [bluePrefix_primalP_add_three, primalP, primalU]
      book3_r := fun r => by
        match r with
        | 0 => norm_num [bluePrefix_zero, primalP, primalU]
        | 1 => norm_num [bluePrefix_primalP_one, primalP, primalU]
        | 2 => norm_num [bluePrefix_primalP_two, primalP, primalU]
        | k + 3 => norm_num [bluePrefix_primalP_add_three, primalP, primalU] }

/-- Theorem 2(a): `699 / 250` is simultaneously a valid global upper bound for every
infinite-depth LP feasible point AND attained with equality at a positive-`n` feasible point. -/
theorem infinite_depth_lp_exact_699_250 :
    (∀ n t a m b p u, IsValidInfiniteHierarchyPoint n t a m b p u →
      t ≤ (699 / 250 : ℚ) * n) ∧
    (∃ n t a m b p u, 0 < n ∧ IsValidInfiniteHierarchyPoint n t a m b p u ∧
      t = (699 / 250 : ℚ) * n) :=
  ⟨fun _ _ _ _ _ _ _ h => infinite_depth_lp_upper h,
   ⟨250, 699, 51, 199, 159, primalP, primalU, by norm_num,
    infinite_depth_lp_attained, by norm_num⟩⟩

end TuzaBound
