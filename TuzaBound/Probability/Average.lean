/-
Copyright (c) 2026 Sichen Wang, Tyler B. Hughes. All rights reserved.
Released under MIT license as described in the file LICENSE.
Adapted and extended from https://github.com/sichen-wang/tuza-lean (Lean v4.32.0 -> v4.35.0, namespace TuzaBound).
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic

/-! Finite rational averages and uniformly chosen Boolean vertex colorings. -/

@[expose] public section

namespace TuzaBound

open scoped BigOperators

variable {Ω : Type*} {Ω' : Type*} {I : Type*} {V : Type*}

/-- The uniform average on a finite type, with values in the rationals. -/
def finiteAverage [Fintype Ω] (f : Ω → ℚ) : ℚ :=
  (∑ ω, f ω) / Fintype.card Ω

/-- The uniform average over all Boolean vertex colorings. -/
def bitAverage [Fintype V] [DecidableEq V] (f : (V → Bool) → ℚ) : ℚ :=
  finiteAverage f

theorem finiteAverage_equiv [Fintype Ω] [Fintype Ω']
    (e : Ω ≃ Ω') (f : Ω' → ℚ) :
    finiteAverage (fun ω => f (e ω)) = finiteAverage f := by
  unfold finiteAverage
  rw [e.sum_comp, Fintype.card_congr e]

theorem finiteAverage_const [Fintype Ω] [Nonempty Ω] (c : ℚ) :
    finiteAverage (fun _ : Ω => c) = c := by
  have hn : (Fintype.card Ω : ℚ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp [finiteAverage, hn]

theorem finiteAverage_add [Fintype Ω] (f g : Ω → ℚ) :
    finiteAverage (fun ω => f ω + g ω) = finiteAverage f + finiteAverage g := by
  simp only [finiteAverage, Finset.sum_add_distrib, add_div]

theorem finiteAverage_finset_sum [Fintype Ω] (s : Finset I) (f : I → Ω → ℚ) :
    finiteAverage (fun ω => ∑ i ∈ s, f i ω) =
      ∑ i ∈ s, finiteAverage (f i) := by
  unfold finiteAverage
  rw [Finset.sum_comm, Finset.sum_div]

theorem finiteAverage_sum [Fintype Ω] [Fintype I] (f : I → Ω → ℚ) :
    finiteAverage (fun ω => ∑ i, f i ω) = ∑ i, finiteAverage (f i) := by
  exact finiteAverage_finset_sum Finset.univ f

theorem finiteAverage_mono [Fintype Ω] (f g : Ω → ℚ)
    (h : ∀ ω, f ω ≤ g ω) : finiteAverage f ≤ finiteAverage g := by
  unfold finiteAverage
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun ω _ => h ω)
    (by positivity)

/-- Some outcome costs no more than its uniform finite average. -/
theorem exists_le_finiteAverage [Fintype Ω] [Nonempty Ω] (f : Ω → ℚ) :
    ∃ ω, f ω ≤ finiteAverage f := by
  classical
  obtain ⟨ω, _, hω⟩ :=
    Finset.exists_min_image (Finset.univ : Finset Ω) f Finset.univ_nonempty
  refine ⟨ω, ?_⟩
  have hn : (0 : ℚ) < Fintype.card Ω := by
    exact_mod_cast Fintype.card_pos
  apply (le_div_iff₀ hn).2
  calc
    f ω * (Fintype.card Ω : ℚ) = ∑ _ : Ω, f ω := by simp [mul_comm]
    _ ≤ ∑ a : Ω, f a := Finset.sum_le_sum fun a ha => hω a ha

/-- Finite-sum accounting: pointwise charges and individual average bounds
produce one outcome obeying the sum of the budgets. -/
theorem exists_le_sum_of_average_le [Fintype Ω] [Nonempty Ω]
    (s : Finset I) (cost : Ω → ℚ) (base : ℚ)
    (charge : I → Ω → ℚ) (budget : I → ℚ)
    (hcost : ∀ ω, cost ω ≤ base + ∑ i ∈ s, charge i ω)
    (hcharge : ∀ i ∈ s, finiteAverage (charge i) ≤ budget i) :
    ∃ ω, cost ω ≤ base + ∑ i ∈ s, budget i := by
  obtain ⟨ω, hω⟩ := exists_le_finiteAverage cost
  refine ⟨ω, hω.trans ?_⟩
  calc
    finiteAverage cost ≤
        finiteAverage (fun ω => base + ∑ i ∈ s, charge i ω) :=
      finiteAverage_mono _ _ hcost
    _ = base + ∑ i ∈ s, finiteAverage (charge i) := by
      rw [finiteAverage_add, finiteAverage_const, finiteAverage_finset_sum]
    _ ≤ base + ∑ i ∈ s, budget i :=
      add_le_add_right (Finset.sum_le_sum hcharge) base

theorem finiteAverage_prod_fst [Fintype Ω] [Fintype Ω']
    [Nonempty Ω] [Nonempty Ω'] (f : Ω → ℚ) :
    finiteAverage (fun p : Ω × Ω' => f p.1) = finiteAverage f := by
  have ha : (Fintype.card Ω : ℚ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hb : (Fintype.card Ω' : ℚ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  unfold finiteAverage
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Fintype.card_prod, Nat.cast_mul]
  rw [← Finset.mul_sum]
  field_simp

/-- Uniform Boolean colorings restrict uniformly to any injective family of vertices. -/
theorem bitAverage_restrict [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
    (v : I → V) (hv : Function.Injective v) (f : (I → Bool) → ℚ) :
    bitAverage (fun χ : V → Bool => f (χ ∘ v)) = bitAverage f := by
  let _ : DecidablePred (fun a : V => a ∈ Set.range v) :=
    fun _ => Classical.propDecidable _
  let e : (V → Bool) ≃
      (I → Bool) × ({a : V // a ∉ Set.range v} → Bool) :=
    (Equiv.piEquivPiSubtypeProd (fun a => a ∈ Set.range v) (fun _ => Bool)).trans
      (Equiv.prodCongr
        (Equiv.arrowCongr (Equiv.ofInjective v hv).symm (Equiv.refl Bool))
        (Equiv.refl _))
  have he (χ : V → Bool) : (e χ).1 = χ ∘ v := by
    rfl
  change finiteAverage (fun χ : V → Bool => f (χ ∘ v)) = finiteAverage f
  calc
    finiteAverage (fun χ : V → Bool => f (χ ∘ v)) =
        finiteAverage (fun χ : V → Bool => f (e χ).1) := by
      simp only [he]
    _ = finiteAverage (fun p :
        (I → Bool) × ({a : V // a ∉ Set.range v} → Bool) => f p.1) :=
      finiteAverage_equiv e (fun p => f p.1)
    _ = finiteAverage f := finiteAverage_prod_fst f

/-- Event that every vertex in `U` receives the fixed Boolean color `b`. -/
def allConstColor (U : Finset V) (b : Bool) (χ : V → Bool) : Prop :=
  ∀ w ∈ U, χ w = b

instance [DecidableEq V] (U : Finset V) (b : Bool) : DecidablePred (allConstColor U b) :=
  fun _ => inferInstanceAs (Decidable (∀ w ∈ U, _ = _))

/-- On a uniform Boolean coloring, `U` is monochromatic of color `b` with probability `(1/2)^|U|`. -/
theorem allConstColor_average [Fintype V] [DecidableEq V] (U : Finset V) (b : Bool) :
    bitAverage (fun χ => if allConstColor U b χ then (1 : ℚ) else 0) =
      (1 / 2 : ℚ) ^ U.card := by
  let g : ({w // w ∈ U} → Bool) → ℚ :=
    fun ψ => if ψ = (fun _ => b) then 1 else 0
  have hcomp :
      (fun χ : V → Bool => if allConstColor U b χ then (1 : ℚ) else 0) =
      (fun χ : V → Bool => g (χ ∘ Subtype.val)) := by
    funext χ
    have hiff : allConstColor U b χ ↔ (χ ∘ Subtype.val) = (fun _ : {w // w ∈ U} => b) := by
      constructor
      · intro h
        funext w
        exact h w.val w.property
      · intro h w hw
        exact congrFun h ⟨w, hw⟩
    simp only [g, hiff]
  rw [hcomp, bitAverage_restrict Subtype.val Subtype.val_injective g]
  unfold bitAverage finiteAverage g
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
    Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]
  push_cast
  rw [one_div, ← inv_pow, one_div]

/-- An edge is noncrossing when its endpoints have the same Boolean color. -/
def sameColor (u v : V) (χ : V → Bool) : Prop := χ u = χ v

/-- Event that `u` and `v` share a Boolean color while at least one `z ∈ S` differs. -/
def spineEvent (u v : V) (S : Finset V) (χ : V → Bool) : Prop :=
  χ u = χ v ∧ ∃ z ∈ S, χ z ≠ χ u

/-- The event allowing an opposite edge of a two-page book to be added. -/
def bookEvent (u v x y : V) (χ : V → Bool) : Prop :=
  χ x = χ y ∧ (χ u ≠ χ x ∨ χ v ≠ χ x)

instance (u v : V) : DecidablePred (sameColor u v) :=
  fun _ => inferInstanceAs (Decidable (_ = _))

instance [DecidableEq V] (u v : V) (S : Finset V) : DecidablePred (spineEvent u v S) :=
  fun _ => inferInstanceAs (Decidable (_ ∧ ∃ z ∈ S, _))

instance (u v x y : V) : DecidablePred (bookEvent u v x y) :=
  fun _ => inferInstanceAs (Decidable (_ ∧ (_ ∨ _)))

/-- Two distinct vertices agree in exactly half of all Boolean colorings. -/
theorem sameColor_average [Fintype V] [DecidableEq V] (u v : V) (huv : u ≠ v) :
    bitAverage (fun χ => if sameColor u v χ then (1 : ℚ) else 0) = 1 / 2 := by
  have hpoint :
      (fun χ : V → Bool => if sameColor u v χ then (1 : ℚ) else 0) =
      (fun χ : V → Bool =>
        (if allConstColor ({u, v} : Finset V) true χ then (1 : ℚ) else 0) +
        (if allConstColor ({u, v} : Finset V) false χ then (1 : ℚ) else 0)) := by
    funext χ
    have ht : allConstColor ({u, v} : Finset V) true χ ↔ χ u = true ∧ χ v = true := by
      simp [allConstColor]
    have hf : allConstColor ({u, v} : Finset V) false χ ↔ χ u = false ∧ χ v = false := by
      simp [allConstColor]
    rw [if_congr ht rfl rfl, if_congr hf rfl rfl]
    rcases Bool.dichotomy (χ u) with h₁ | h₁ <;>
      rcases Bool.dichotomy (χ v) with h₂ | h₂ <;>
      simp [sameColor, h₁, h₂]
  rw [hpoint]
  change finiteAverage _ = 1 / 2
  rw [finiteAverage_add]
  change bitAverage _ + bitAverage _ = 1 / 2
  rw [allConstColor_average, allConstColor_average, Finset.card_pair huv]
  norm_num

/-- Exact marginal probability `1/2 - (1/2)^(|S| + 1)` of `spineEvent u v S`
when `u ≠ v` and `u, v ∉ S`. -/
theorem spineEvent_average [Fintype V] [DecidableEq V] (u v : V) (S : Finset V)
    (huv : u ≠ v) (huS : u ∉ S) (hvS : v ∉ S) :
    bitAverage (fun χ => if spineEvent u v S χ then (1 : ℚ) else 0) =
      1 / 2 - (1 / 2 : ℚ) ^ (S.card + 1) := by
  let U : Finset V := insert u (insert v S)
  have huIns : u ∉ insert v S := by simp [huv, huS]
  have hUcard : U.card = S.card + 2 := by
    rw [Finset.card_insert_of_notMem huIns, Finset.card_insert_of_notMem hvS]
  have hpoint :
      (fun χ : V → Bool =>
        (if spineEvent u v S χ then (1 : ℚ) else 0) +
        ((if allConstColor U true χ then (1 : ℚ) else 0) +
         (if allConstColor U false χ then (1 : ℚ) else 0))) =
      (fun χ : V → Bool => if sameColor u v χ then (1 : ℚ) else 0) := by
    funext χ
    have huU : u ∈ U := Finset.mem_insert_self u _
    have hvU : v ∈ U := Finset.mem_insert_of_mem (Finset.mem_insert_self v S)
    by_cases hsc : χ u = χ v
    · by_cases hex : ∃ z ∈ S, χ z ≠ χ u
      · have hsp : spineEvent u v S χ := ⟨hsc, hex⟩
        obtain ⟨z, hzS, hz⟩ := hex
        have hzU : z ∈ U :=
          Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hzS)
        have hnt : ¬ allConstColor U true χ := by
          intro hall
          exact hz ((hall z hzU).trans (hall u huU).symm)
        have hnf : ¬ allConstColor U false χ := by
          intro hall
          exact hz ((hall z hzU).trans (hall u huU).symm)
        simp [sameColor, hsc, hsp, hnt, hnf]
      · have hnsp : ¬ spineEvent u v S χ := fun h => hex h.2
        push Not at hex
        cases hu : χ u
        · have hf : allConstColor U false χ := by
            intro w hw
            rcases Finset.mem_insert.mp hw with rfl | hw
            · exact hu
            · rcases Finset.mem_insert.mp hw with rfl | hwS
              · exact hsc.symm.trans hu
              · exact (hex w hwS).trans hu
          have hnt : ¬ allConstColor U true χ := by
            intro hall
            have := hall u huU
            rw [hu] at this
            exact Bool.false_ne_true this
          simp [sameColor, hsc, hnsp, hf, hnt]
        · have ht : allConstColor U true χ := by
            intro w hw
            rcases Finset.mem_insert.mp hw with rfl | hw
            · exact hu
            · rcases Finset.mem_insert.mp hw with rfl | hwS
              · exact hsc.symm.trans hu
              · exact (hex w hwS).trans hu
          have hnf : ¬ allConstColor U false χ := by
            intro hall
            have := hall u huU
            rw [hu] at this
            cases this
          simp [sameColor, hsc, hnsp, ht, hnf]
    · have hnsp : ¬ spineEvent u v S χ := fun h => hsc h.1
      have hnt : ¬ allConstColor U true χ :=
        fun hall => hsc ((hall u huU).trans (hall v hvU).symm)
      have hnf : ¬ allConstColor U false χ :=
        fun hall => hsc ((hall u huU).trans (hall v hvU).symm)
      simp [sameColor, hsc, hnsp, hnt, hnf]
  have havg := congrArg bitAverage hpoint
  unfold bitAverage at havg
  rw [finiteAverage_add, finiteAverage_add] at havg
  change bitAverage _ + (bitAverage _ + bitAverage _) = bitAverage _ at havg
  rw [allConstColor_average, allConstColor_average, sameColor_average u v huv, hUcard] at havg
  have hpow : (1 / 2 : ℚ) ^ (S.card + 2) + (1 / 2 : ℚ) ^ (S.card + 2) =
      (1 / 2 : ℚ) ^ (S.card + 1) := by ring
  linarith

/-- The book event occurs in six of the sixteen local Boolean colorings (`3 / 8`). -/
theorem bookEvent_average [Fintype V] [DecidableEq V] (u v x y : V)
    (huv : u ≠ v) (hux : u ≠ x) (huy : u ≠ y)
    (hvx : v ≠ x) (hvy : v ≠ y) (hxy : x ≠ y) :
    bitAverage (fun χ => if bookEvent u v x y χ then (1 : ℚ) else 0) = 3 / 8 := by
  have heq : (fun χ : V → Bool => if bookEvent u v x y χ then (1 : ℚ) else 0) =
      (fun χ : V → Bool => if spineEvent x y ({u, v} : Finset V) χ then (1 : ℚ) else 0) := by
    funext χ
    apply if_congr _ rfl rfl
    simp [bookEvent, spineEvent]
  have hxnot : x ∉ ({u, v} : Finset V) := by simp [hux.symm, hvx.symm]
  have hynot : y ∉ ({u, v} : Finset V) := by simp [huy.symm, hvy.symm]
  rw [heq, spineEvent_average x y ({u, v} : Finset V) hxy hxnot hynot,
    Finset.card_pair huv]
  norm_num

theorem bookEvent_average_of_injective [Fintype V] [DecidableEq V] (u v x y : V)
    (h : Function.Injective (![u, v, x, y] : Fin 4 → V)) :
    bitAverage (fun χ => if bookEvent u v x y χ then (1 : ℚ) else 0) = 3 / 8 := by
  have h01 : (0 : Fin 4) ≠ 1 := by decide
  have h02 : (0 : Fin 4) ≠ 2 := by decide
  have h03 : (0 : Fin 4) ≠ 3 := by decide
  have h12 : (1 : Fin 4) ≠ 2 := by decide
  have h13 : (1 : Fin 4) ≠ 3 := by decide
  have h23 : (2 : Fin 4) ≠ 3 := by decide
  exact bookEvent_average u v x y
    (fun he => h01 (h (by simpa using he)))
    (fun he => h02 (h (by simpa using he)))
    (fun he => h03 (h (by simpa using he)))
    (fun he => h12 (h (by simpa using he)))
    (fun he => h13 (h (by simpa using he)))
    (fun he => h23 (h (by simpa using he)))

end TuzaBound
