/-
Copyright (c) 2026 Sichen Wang. All rights reserved.
Released under MIT license as described in the file LICENSE.
Adapted and extended from https://github.com/sichen-wang/tuza-lean (Lean v4.32.0 -> v4.35.0, namespace TuzaBound).
-/
module

public import Mathlib.Tactic

/-! The arithmetic combining the colored and full-graph covers. -/

@[expose] public section

namespace TuzaBound

/-- Arithmetic in the first colored-cover comparison, with denominators cleared. -/
theorem colored_bound_arithmetic {t p a r u : ℕ}
    (hfirst : t + 2 * a + u ≤ 3 * p + r)
    (hsecond : t + r ≤ 2 * p + 3 * a) (hra : r ≤ a) :
    3 * t + 2 * u ≤ 8 * p := by
  omega

/-- Arithmetic after applying the first colored estimate to the residual family. -/
theorem colored_refined_arithmetic {t p a r u : ℕ}
    (hfirst : t + 2 * a + u ≤ 3 * p + r)
    (hresidual : 3 * t + 2 * r ≤ 6 * p + 8 * a) :
    4 * t + u ≤ 9 * p + 6 * a := by
  omega

/-- Sichen Wang's equations (3)--(6), combined with weights 20, 8, 19, and 12. -/
theorem four_bounds_arithmetic {t n a b c d h : ℕ}
    (hfirst : t + a ≤ 3 * n)
    (hcut : 8 * t + 8 * c ≤ 12 * n + 20 * a + 12 * b + 3 * h)
    (hbooks : t + c + d ≤ 3 * n)
    (hcolored : 4 * t + 4 * b + h ≤ 12 * n + 9 * c + 6 * d) :
    59 * t + d ≤ 165 * n := by
  omega

/-- Equations (3), (4'), (5), (6a), and (6c), combined with rational weights
`(85, 34, 80, 12, 39)` (cleared to integer weights `(170, 17, 160, 24, 26)`),
yielding `500 * t + 7 * h + 28 * h1 ≤ 1398 * n` and hence `250 * t ≤ 699 * n`. -/
theorem five_bounds_arithmetic {t n a b c d h h1 : ℕ}
    (hfirst : t + a ≤ 3 * n)
    (hcut : 4 * t + 4 * c ≤ 6 * n + 10 * a + 6 * b + h)
    (hbooks : t + c + d ≤ 3 * n)
    (hcolA : t + b + 2 * d + h ≤ 3 * n + 3 * c + h1)
    (hcolC : 3 * t + 3 * b + 2 * h1 ≤ 9 * n + 6 * c + 8 * d) :
    500 * t + 7 * h + 28 * h1 ≤ 1398 * n := by
  omega

theorem five_bounds_arithmetic_250_699 {t n a b c d h h1 : ℕ}
    (hfirst : t + a ≤ 3 * n)
    (hcut : 4 * t + 4 * c ≤ 6 * n + 10 * a + 6 * b + h)
    (hbooks : t + c + d ≤ 3 * n)
    (hcolA : t + b + 2 * d + h ≤ 3 * n + 3 * c + h1)
    (hcolC : 3 * t + 3 * b + 2 * h1 ≤ 9 * n + 6 * c + 8 * d) :
    250 * t ≤ 699 * n := by
  have h500 := five_bounds_arithmetic hfirst hcut hbooks hcolA hcolC
  omega

/-- Equations (3), unrelaxed (4''), (5), opposite-elimination (5''), and elementary
non-recursive colored covers (6a) (with `h_hat + h0 = h`) and (6b), combined with
integer weights `(10, 1, 8, 1, 2, 4)` (corresponding to `(10, 4, 8, 1, 2, 4)` on the
fractional forms), yielding `29 * t + 2 * h1 ≤ 81 * n`. -/
theorem six_bounds_arithmetic_29_81 {t n a b c d h h_hat h0 h1 : ℕ}
    (hh : h_hat + h0 = h)
    (hb3 : t + a ≤ 3 * n)
    (hb4pp : 4 * t + 4 * c ≤ 6 * n + 10 * a + 6 * b + h_hat)
    (hb5 : t + c + d ≤ 3 * n)
    (hb5pp : t + 2 * c ≤ 3 * n + h_hat + 2 * h0)
    (hb6a : t + b + 2 * d + h ≤ 3 * n + 3 * c + h1)
    (hb6b : t + b + h1 ≤ 3 * n + 2 * c + 3 * d) :
    29 * t + 2 * h1 ≤ 81 * n := by
  omega

theorem six_bounds_arithmetic_29_81_simple {t n a b c d h h_hat h0 h1 : ℕ}
    (hh : h_hat + h0 = h)
    (hb3 : t + a ≤ 3 * n)
    (hb4pp : 4 * t + 4 * c ≤ 6 * n + 10 * a + 6 * b + h_hat)
    (hb5 : t + c + d ≤ 3 * n)
    (hb5pp : t + 2 * c ≤ 3 * n + h_hat + 2 * h0)
    (hb6a : t + b + 2 * d + h ≤ 3 * n + 3 * c + h1)
    (hb6b : t + b + h1 ≤ 3 * n + 2 * c + 3 * d) :
    29 * t ≤ 81 * n := by
  have h29 := six_bounds_arithmetic_29_81 hh hb3 hb4pp hb5 hb5pp hb6a hb6b
  omega

end TuzaBound
