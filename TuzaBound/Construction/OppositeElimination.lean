/-
Copyright (c) 2026 Tyler B. Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Complete opposite-edge elimination in C^(5) (Theorem 1.1, inequality (5'')) for `TuzaBound`.
-/
module

public import TuzaBound.Construction.HelperArborescence
public import TuzaBound.Construction.BookCover

/-!
# Theorem 1.1: Complete Opposite-Edge Elimination in `C^(5)` (`(5'')`)

Under lexicographic maximality (`max b`, then `max m`) of `P' = c.rest` in `G'`, zero non-private
two-page books `i ∈ I_np` can carry an uncovered opposite edge `w_i x_i` into `O' \ B(P')`, into
any non-private book `k ∈ I_np \ {i}`, or into any sink book `k ∈ B_out`. Partitioning the `h`
private pages `I_priv` of `Q = r.second` into `B_out` (size `h_hat`) and `I_{priv,0} = I_priv \ B_out`
(size `h_0`, `h_hat + h_0 = h`), the deterministic edge set

`C_core := E(A) ∪ E(P' \ {T_i : i ∈ I_np ⊔ B_out}) ∪ R({T_i : i ∈ I_np ⊔ B_out}) ∪ {w_k x_k : k ∈ B_out}`

meets every triangle of `G` and satisfies inequality `(5'')`:

`τ(G) + 2 * c ≤ 3 * n + h_hat + 2 * h_0`.
-/

@[expose] public section

namespace TuzaBound

open Finset
open scoped BigOperators

section LexExchanges

variable {E : Type*} [DecidableEq E]

omit [DecidableEq E] in
theorem nonempty_ne_of_disjoint {A B : Finset E} (hA : A.Nonempty) (hd : Disjoint A B) :
    A ≠ B := by
  rintro rfl
  obtain ⟨e, he⟩ := hA
  exact disjoint_left.mp hd he he

theorem notMem_of_disjoint_support {P : Finset (Finset E)} {A : Finset E}
    (hA : A.Nonempty) (hd : Disjoint A (support P)) : A ∉ P := by
  intro hmem
  obtain ⟨e, he⟩ := hA
  exact disjoint_left.mp hd he (mem_support.mpr ⟨A, hmem, he⟩)

/-- **1-for-2 Lexicographic Exchange Obstruction**: In a lexicographically maximum packing `P`
(maximizing `|P ∩ S|` then `|P|`), one cannot replace a single `p ∈ P ∩ S` by a disjoint pair
`{Z, U}` with `Z ∈ S` and `U ∈ F`. -/
theorem IsLexMaximumPacking.no_one_to_two {F S P : Finset (Finset E)}
    (hP : IsLexMaximumPacking F S P) (hSF : S ⊆ F)
    {p Z U : Finset E} (hp : p ∈ P ∩ S) (hZ : Z ∈ S) (hU : U ∈ F)
    (hZne : Z.Nonempty) (hUne : U.Nonempty)
    (hdUZ : Disjoint U Z)
    (hdZp : Disjoint Z (support (P.erase p)))
    (hdUp : Disjoint U (support (P.erase p))) : False := by
  let P₀ := P.erase p
  have hpP : p ∈ P := (mem_inter.mp hp).1
  have hP₀ : IsPacking F P₀ := hP.1.subfamily (erase_subset p P)
  have hZnotP₀ : Z ∉ P₀ := notMem_of_disjoint_support hZne hdZp
  have hP₁ : IsPacking F (insert Z P₀) := packing_insert hP₀ (hSF hZ) hdZp
  have hdUP₁ : Disjoint U (support (insert Z P₀)) := by
    rw [support_insert]
    exact disjoint_union_right.mpr ⟨hdUZ, hdUp⟩
  have hUnotP₁ : U ∉ insert Z P₀ := notMem_of_disjoint_support hUne hdUP₁
  let Q := insert U (insert Z P₀)
  have hQ : IsPacking F Q := packing_insert hP₁ hU hdUP₁
  have hcardP₀ : P₀.card + 1 = P.card := card_erase_add_one hpP
  have hcardQ : Q.card = P.card + 1 := by
    change (insert U (insert Z P₀)).card = P.card + 1
    rw [card_insert_of_notMem hUnotP₁, card_insert_of_notMem hZnotP₀]
    omega
  have hsubS : insert Z ((P ∩ S).erase p) ⊆ Q ∩ S := by
    intro X hX
    rcases mem_insert.mp hX with rfl | hX'
    · exact mem_inter.mpr ⟨mem_insert_of_mem (mem_insert_self _ _), hZ⟩
    · obtain ⟨hXne, hXPS⟩ := mem_erase.mp hX'
      obtain ⟨hXP, hXS⟩ := mem_inter.mp hXPS
      exact mem_inter.mpr ⟨mem_insert_of_mem (mem_insert_of_mem (mem_erase.mpr ⟨hXne, hXP⟩)), hXS⟩
  have hZnotPS : Z ∉ (P ∩ S).erase p := by
    intro hmem
    obtain ⟨hZne_p, hZPS⟩ := mem_erase.mp hmem
    exact hZnotP₀ (mem_erase.mpr ⟨hZne_p, (mem_inter.mp hZPS).1⟩)
  have hScard_ge : (P ∩ S).card ≤ (Q ∩ S).card := by
    have hc := card_le_card hsubS
    rw [card_insert_of_notMem hZnotPS, card_erase_add_one hp] at hc
    exact hc
  obtain ⟨hSle, hQle⟩ := hP.2 Q hQ
  have hSeq : (Q ∩ S).card = (P ∩ S).card := Nat.le_antisymm hSle hScard_ge
  have hle := hQle hSeq
  omega

/-- **2-for-3 Lexicographic Exchange Obstruction**: In a lexicographically maximum packing `P`
(maximizing `|P ∩ S|` then `|P|`), one cannot replace two distinct `p₁, p₂ ∈ P ∩ S` by three
pairwise disjoint nonempty sets `{Z₁, Z₂, U}` with `Z₁, Z₂ ∈ S` and `U ∈ F`. -/
theorem IsLexMaximumPacking.no_two_to_three {F S P : Finset (Finset E)}
    (hP : IsLexMaximumPacking F S P) (hSF : S ⊆ F)
    {p₁ p₂ Z₁ Z₂ U : Finset E}
    (hp₁ : p₁ ∈ P ∩ S) (hp₂ : p₂ ∈ P ∩ S) (hne12 : p₁ ≠ p₂)
    (hZ₁ : Z₁ ∈ S) (hZ₂ : Z₂ ∈ S) (hU : U ∈ F)
    (hZ₁ne : Z₁.Nonempty) (hZ₂ne : Z₂.Nonempty) (hUne : U.Nonempty)
    (hdZ : Disjoint Z₁ Z₂) (hdUZ₁ : Disjoint U Z₁) (hdUZ₂ : Disjoint U Z₂)
    (hdZ₁p : Disjoint Z₁ (support ((P.erase p₁).erase p₂)))
    (hdZ₂p : Disjoint Z₂ (support ((P.erase p₁).erase p₂)))
    (hdUp : Disjoint U (support ((P.erase p₁).erase p₂))) : False := by
  let P₀ := (P.erase p₁).erase p₂
  have hp₁P : p₁ ∈ P := (mem_inter.mp hp₁).1
  have hp₂P : p₂ ∈ P := (mem_inter.mp hp₂).1
  have hp₂P1 : p₂ ∈ P.erase p₁ := mem_erase.mpr ⟨hne12.symm, hp₂P⟩
  have hP₀ : IsPacking F P₀ := hP.1.subfamily ((erase_subset p₂ _).trans (erase_subset p₁ P))
  have hZ₁notP₀ : Z₁ ∉ P₀ := notMem_of_disjoint_support hZ₁ne hdZ₁p
  have hP₁ : IsPacking F (insert Z₁ P₀) := packing_insert hP₀ (hSF hZ₁) hdZ₁p
  have hdZ₂P₁ : Disjoint Z₂ (support (insert Z₁ P₀)) := by
    rw [support_insert]
    exact disjoint_union_right.mpr ⟨hdZ.symm, hdZ₂p⟩
  have hZ₂notP₁ : Z₂ ∉ insert Z₁ P₀ := notMem_of_disjoint_support hZ₂ne hdZ₂P₁
  have hP₂ : IsPacking F (insert Z₂ (insert Z₁ P₀)) := packing_insert hP₁ (hSF hZ₂) hdZ₂P₁
  have hdUP₂ : Disjoint U (support (insert Z₂ (insert Z₁ P₀))) := by
    rw [support_insert, support_insert]
    exact disjoint_union_right.mpr ⟨hdUZ₂, disjoint_union_right.mpr ⟨hdUZ₁, hdUp⟩⟩
  have hUnotP₂ : U ∉ insert Z₂ (insert Z₁ P₀) := notMem_of_disjoint_support hUne hdUP₂
  let Q := insert U (insert Z₂ (insert Z₁ P₀))
  have hQ : IsPacking F Q := packing_insert hP₂ hU hdUP₂
  have hcardP1 : (P.erase p₁).card + 1 = P.card := card_erase_add_one hp₁P
  have hcardP₀ : P₀.card + 1 = (P.erase p₁).card := card_erase_add_one hp₂P1
  have hcardQ : Q.card = P.card + 1 := by
    change (insert U (insert Z₂ (insert Z₁ P₀))).card = P.card + 1
    rw [card_insert_of_notMem hUnotP₂, card_insert_of_notMem hZ₂notP₁,
      card_insert_of_notMem hZ₁notP₀]
    omega
  let S₀ := ((P ∩ S).erase p₁).erase p₂
  have hp₂PS1 : p₂ ∈ (P ∩ S).erase p₁ := mem_erase.mpr ⟨hne12.symm, hp₂⟩
  have hS₀card1 : ((P ∩ S).erase p₁).card + 1 = (P ∩ S).card := card_erase_add_one hp₁
  have hS₀card0 : S₀.card + 1 = ((P ∩ S).erase p₁).card := card_erase_add_one hp₂PS1
  have hS₀sub : S₀ ⊆ P₀ := by
    intro X hX
    obtain ⟨hne2, hX1⟩ := mem_erase.mp hX
    obtain ⟨hne1, hXPS⟩ := mem_erase.mp hX1
    exact mem_erase.mpr ⟨hne2, mem_erase.mpr ⟨hne1, (mem_inter.mp hXPS).1⟩⟩
  have hZ₁notS₀ : Z₁ ∉ S₀ := fun h => hZ₁notP₀ (hS₀sub h)
  have hZ₂notS₁ : Z₂ ∉ insert Z₁ S₀ := by
    intro h
    rcases mem_insert.mp h with rfl | hS
    · exact nonempty_ne_of_disjoint hZ₁ne hdZ rfl
    · exact hZ₂notP₁ (mem_insert_of_mem (hS₀sub hS))
  have hsubS : insert Z₂ (insert Z₁ S₀) ⊆ Q ∩ S := by
    intro X hX
    rcases mem_insert.mp hX with rfl | hX1
    · exact mem_inter.mpr ⟨mem_insert_of_mem (mem_insert_self _ _), hZ₂⟩
    · rcases mem_insert.mp hX1 with rfl | hX0
      · exact mem_inter.mpr ⟨mem_insert_of_mem (mem_insert_of_mem (mem_insert_self _ _)), hZ₁⟩
      · have hXS : X ∈ S := (mem_inter.mp (mem_erase.mp (mem_erase.mp hX0).2).2).2
        exact mem_inter.mpr
          ⟨mem_insert_of_mem (mem_insert_of_mem (mem_insert_of_mem (hS₀sub hX0))), hXS⟩
  have hScard_ge : (P ∩ S).card ≤ (Q ∩ S).card := by
    have hc := card_le_card hsubS
    rw [card_insert_of_notMem hZ₂notS₁, card_insert_of_notMem hZ₁notS₀] at hc
    omega
  obtain ⟨hSle, hQle⟩ := hP.2 Q hQ
  have hSeq : (Q ∩ S).card = (P ∩ S).card := Nat.le_antisymm hSle hScard_ge
  have hle := hQle hSeq
  omega

end LexExchanges

namespace OppositeElimination

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {edges : Finset (Sym2 V)} (c : Construction edges)

section Partition

variable {Q : Finset (Finset (Sym2 V))} (hQ : IsPacking c.specialFamily Q)

/-- Private pages `I_priv` of `Q` in `c.specialFamily` (size `h`). -/
noncomputable def privPages (Q : Finset (Finset (Sym2 V))) : Finset (Finset (Sym2 V)) :=
  privateRedPages c.specialFamily c.newEdges Q

/-- Child pages in `Q` belonging to sink books `B_out = helperRoots c hQ` (size `h_hat`). -/
noncomputable def rootPages : Finset (Finset (Sym2 V)) := by
  classical
  exact Q.filter (fun q => ∃ k ∈ HelperArborescence.helperRoots c hQ,
    q ∈ (TwoLayer.book c hQ k).pages)

/-- Remaining private pages `I_{priv,0} := I_priv \ rootPages` (size `h_0 = h - h_hat`). -/
noncomputable def privZeroPages : Finset (Finset (Sym2 V)) :=
  privPages c Q \ rootPages c hQ

/-- Active second pages `K := Q \ I_{priv,0} = I_np ⊔ rootPages` (size `c - h_0`). -/
noncomputable def activePages : Finset (Finset (Sym2 V)) :=
  Q \ privZeroPages c hQ

@[simp] theorem mem_rootPages {q : Finset (Sym2 V)} :
    q ∈ rootPages c hQ ↔ q ∈ Q ∧
      ∃ k ∈ HelperArborescence.helperRoots c hQ, q ∈ (TwoLayer.book c hQ k).pages := by
  classical
  simp [rootPages]

/-- Every `B_out` child page in `Q` has a private red spine in `c.specialFamily`
(Wang's Lemma 2.1, `OppositeEdges.book_child_private`). -/
theorem rootPages_subset_privPages : rootPages c hQ ⊆ privPages c Q := by
  intro q hq
  obtain ⟨hqQ, k, hk, hqk⟩ := (mem_rootPages c hQ).mp hq
  obtain ⟨e, hop, he, heout⟩ := mem_oppositeBooks.mp hk
  exact OppositeEdges.book_child_private c hQ (TwoLayer.book c hQ k)
    k.property (TwoLayer.book_parent_mem c hQ k) hqQ hqk
    (TwoLayer.book_spine_mem c hQ k) hop (c.remaining_sdiff_oldRemaining ▸ he) heout

/-- Exact bijection between `B_out` (`helperRoots c hQ`) and `rootPages c hQ`. -/
theorem rootPages_card_eq :
    (rootPages c hQ).card = (HelperArborescence.helperRoots c hQ).card := by
  classical
  let roots := HelperArborescence.helperRoots c hQ
  have hex : ∀ k : {j // j ∈ roots},
      ∃ q, q ∈ rootPages c hQ ∧ q ∈ (TwoLayer.book c hQ k.val).pages := by
    intro k
    obtain ⟨e, hop, _, _⟩ := mem_oppositeBooks.mp k.property
    obtain ⟨q, hqQ, hqk⟩ := TwoLayer.book_child_of_opposite c hQ k.val hop
    exact ⟨q, (mem_rootPages c hQ).mpr ⟨hqQ, k.val, k.property, hqk⟩, hqk⟩
  choose f hfRoot hfPage using hex
  have hinj : Function.Injective f := by
    intro k₁ k₂ heq
    by_contra hne
    have hval : k₁.val ≠ k₂.val := fun h => hne (Subtype.ext h)
    have hqQ : f k₁ ∈ Q := ((mem_rootPages c hQ).mp (hfRoot k₁)).1
    obtain ⟨e, he⟩ := c.specialFamily_colored.member_nonempty (hQ.1 hqQ)
    exact disjoint_left.mp (TwoLayer.books_disjoint c hQ hval)
      (mem_support.mpr ⟨f k₁, hfPage k₁, he⟩)
      (mem_support.mpr ⟨f k₂, hfPage k₂, heq ▸ he⟩)
  have himg : univ.image f = rootPages c hQ := by
    ext q
    constructor
    · intro hq
      obtain ⟨k, _, rfl⟩ := mem_image.mp hq
      exact hfRoot k
    · intro hq
      obtain ⟨hqQ, k, hk, hqk⟩ := (mem_rootPages c hQ).mp hq
      refine mem_image.mpr ⟨⟨k, hk⟩, mem_univ _, ?_⟩
      have hfkQ : f ⟨k, hk⟩ ∈ Q := ((mem_rootPages c hQ).mp (hfRoot ⟨k, hk⟩)).1
      have hfkP := hfPage ⟨k, hk⟩
      rw [TwoLayer.book_pages] at hqk hfkP
      rcases Layered.mem_twoLayerPages.mp hqk with rfl | ⟨_, hred1⟩
      · exact (OppositeEdges.special_member_not_typeTwo c hQ hqQ k.property).elim
      · rcases Layered.mem_twoLayerPages.mp hfkP with heqP | ⟨_, hred2⟩
        · exact (OppositeEdges.special_member_not_typeTwo c hQ hfkQ (heqP ▸ k.property)).elim
        · exact (TwoLayer.residual_packing c hQ).red_inter_injective
            (typeTwo_colored c.remainingEdges c.old).residual hfkQ hqQ (hred2.trans hred1.symm)
  rw [← himg, card_image_of_injective _ hinj]
  simp [roots]

theorem privZeroPages_subset_Q : privZeroPages c hQ ⊆ Q :=
  sdiff_subset.trans (privateRedPages_subset _ _ _)

/-- Exact partition `h_hat + h_0 = h` (`|helperRoots| + |privZeroPages| = |privPages|`). -/
theorem helperRoots_add_privZeroPages_card :
    (HelperArborescence.helperRoots c hQ).card + (privZeroPages c hQ).card =
      (privPages c Q).card := by
  have hs := card_sdiff_add_card_eq_card (rootPages_subset_privPages c hQ)
  rw [rootPages_card_eq c hQ] at hs
  change (privZeroPages c hQ).card + (HelperArborescence.helperRoots c hQ).card =
    (privPages c Q).card at hs
  omega

/-- Exact partition `|activePages| + h_0 = |Q|`. -/
theorem activePages_add_privZeroPages_card :
    (activePages c hQ).card + (privZeroPages c hQ).card = Q.card :=
  card_sdiff_add_card_eq_card (privZeroPages_subset_Q c hQ)

theorem activePages_subset_Q : activePages c hQ ⊆ Q := sdiff_subset

theorem activePages_packing : IsPacking c.specialFamily (activePages c hQ) :=
  hQ.subfamily sdiff_subset

theorem mem_activePages_iff {q : Finset (Sym2 V)} :
    q ∈ activePages c hQ ↔ q ∈ Q ∧ (q ∉ privPages c Q ∨ q ∈ rootPages c hQ) := by
  simp only [activePages, privZeroPages, mem_sdiff]
  tauto

end Partition

section CoreBooks

/-- Two-layer books on `c.rest` formed by attaching active second pages `K ⊆ c.specialFamily`. -/
def corePages (K : Finset (Finset (Sym2 V))) (p : {T // T ∈ c.rest}) :
    Finset (Finset (Sym2 V)) :=
  Layered.twoLayerPages c.newEdges c.rest K p

/-- Parents in `c.rest` that are paired with a child in `K`. -/
noncomputable def pairedRest (K : Finset (Finset (Sym2 V))) : Finset (Finset (Sym2 V)) := by
  classical
  exact c.rest.filter (fun p => ∃ q ∈ K, q ∩ c.newEdges = p ∩ c.newEdges)

@[simp] theorem mem_pairedRest {K : Finset (Finset (Sym2 V))} {p : Finset (Sym2 V)} :
    p ∈ pairedRest c K ↔ p ∈ c.rest ∧ ∃ q ∈ K, q ∩ c.newEdges = p ∩ c.newEdges := by
  classical
  simp [pairedRest]

theorem pairedRest_subset_rest (K : Finset (Finset (Sym2 V))) :
    pairedRest c K ⊆ c.rest := filter_subset _ _

theorem pairedRest_subset_typeTwo {K : Finset (Finset (Sym2 V))}
    (hK : IsPacking c.specialFamily K) :
    pairedRest c K ⊆ c.typeTwo := by
  intro p hp
  obtain ⟨hpR, q, hqK, hred⟩ := (mem_pairedRest c).mp hp
  apply (ThreeLayer.parent_typeTwo_iff_red_nonempty ⟨p, hpR⟩).mpr
  rw [← hred]
  exact card_pos.mp (by rw [(c.specialFamily_colored q (hK.1 hqK)).2]; decide)

theorem corePages_subset_family {K : Finset (Finset (Sym2 V))}
    (hK : IsPacking c.specialFamily K) (p : {T // T ∈ c.rest}) :
    corePages c K p ⊆ trianglesOn c.remainingEdges := by
  intro T hT
  rcases Layered.mem_twoLayerPages.mp hT with rfl | ⟨hTK, _⟩
  · exact c.rest_packing.1 p.property
  · exact c.specialFamily_subset_triangles (hK.1 hTK)

theorem coreBook_inter_rest_subset {K : Finset (Finset (Sym2 V))}
    (hK : IsPacking c.specialFamily K) (p : {T // T ∈ c.rest}) :
    support (corePages c K p) ∩ support c.rest ⊆ p.val := by
  intro e he
  obtain ⟨heb, heP⟩ := mem_inter.mp he
  obtain ⟨T, hT, heT⟩ := mem_support.mp heb
  rcases Layered.mem_twoLayerPages.mp hT with rfl | ⟨hTK, hTR⟩
  · exact heT
  · have heR : e ∈ T ∩ c.newEdges :=
      ThreeLayer.special_inter_rest (hK.1 hTK) ▸ mem_inter.mpr ⟨heT, heP⟩
    exact (mem_inter.mp (hTR ▸ heR)).1

theorem coreSupports_disjoint {K : Finset (Finset (Sym2 V))}
    (hK : IsPacking c.specialFamily K) :
    Books.DisjointSupports (corePages c K) := by
  intro p p' hne
  have hval : p.val ≠ p'.val := fun h => hne (Subtype.ext h)
  have hd := c.rest_packing.2 p.property p'.property hval
  apply disjoint_left.mpr
  intro e he he'
  obtain ⟨T, hT, heT⟩ := mem_support.mp he
  obtain ⟨U, hU, heU⟩ := mem_support.mp he'
  rcases Layered.mem_twoLayerPages.mp hT with rfl | ⟨hTK, hTR⟩
  · have hep' := coreBook_inter_rest_subset c hK p'
      (mem_inter.mpr ⟨he', mem_support.mpr ⟨p.val, p.property, heT⟩⟩)
    exact disjoint_left.mp hd heT hep'
  · rcases Layered.mem_twoLayerPages.mp hU with rfl | ⟨hUK, hUR⟩
    · have hep := coreBook_inter_rest_subset c hK p
        (mem_inter.mpr ⟨he, mem_support.mpr ⟨p'.val, p'.property, heU⟩⟩)
      exact disjoint_left.mp hd hep heU
    · by_cases hTU : T = U
      · subst hTU
        exact hne (ThreeLayer.owner_unique (hK.1 hTK) p p' hTR hUR)
      · exact disjoint_left.mp (hK.2 hTK hUK hTU) heT heU

theorem corePage_typeTwo_iff_parent {K : Finset (Finset (Sym2 V))}
    (hK : IsPacking c.specialFamily K) (p : {T // T ∈ c.rest})
    {T : Finset (Sym2 V)} (hT : T ∈ corePages c K p) :
    T ∈ typeFamily c.remainingEdges c.old 2 ↔ p.val ∈ c.typeTwo := by
  rcases Layered.mem_twoLayerPages.mp hT with rfl | ⟨hTK, hTR⟩
  · exact ⟨fun h => mem_inter.mpr ⟨p.property, h⟩, fun h => (mem_inter.mp h).2⟩
  · have hc := hK.1 hTK
    have hp : p.val ∈ c.typeTwo := by
      apply (ThreeLayer.parent_typeTwo_iff_red_nonempty p).mpr
      rw [← hTR]
      exact card_pos.mp (by rw [(c.specialFamily_colored T hc).2]; decide)
    exact ⟨fun _ => hp, fun _ => c.specialFamily_subset_typeTwo hc⟩

theorem coreChoices_lexMaximum {K : Finset (Finset (Sym2 V))}
    (hK : IsPacking c.specialFamily K)
    {f : {T // T ∈ c.rest} → Finset (Sym2 V)}
    (hf : Books.ChoosesPages (corePages c K) f) :
    IsLexMaximumPacking (trianglesOn c.remainingEdges)
      (typeFamily c.remainingEdges c.old 2) (Books.choice f) := by
  classical
  have hpack := Books.choice_isPacking (corePages_subset_family c hK)
    (coreSupports_disjoint c hK) hf
  have hcard : (Books.choice f).card = c.rest.card := by
    simpa using Books.card_choice (coreSupports_disjoint c hK)
      (fun p T hT => trianglesOn_nonempty (corePages_subset_family c hK p hT)) hf
  have heq : Books.choice f ∩ typeFamily c.remainingEdges c.old 2 =
      univ.image (fun p : {T // T ∈ c.typeTwo} =>
        f ⟨p.val, c.typeTwo_subset_rest p.property⟩) := by
    ext T
    constructor
    · intro hT
      obtain ⟨hTf, hTtype⟩ := mem_inter.mp hT
      obtain ⟨p, rfl⟩ := Books.mem_choice.mp hTf
      have hp := (corePage_typeTwo_iff_parent c hK p (hf p)).mp hTtype
      exact mem_image.mpr ⟨⟨p.val, hp⟩, mem_univ _, rfl⟩
    · intro hT
      obtain ⟨p, _, rfl⟩ := mem_image.mp hT
      exact mem_inter.mpr
        ⟨Books.mem_choice.mpr ⟨⟨p.val, c.typeTwo_subset_rest p.property⟩, rfl⟩,
          (corePage_typeTwo_iff_parent c hK ⟨p.val, c.typeTwo_subset_rest p.property⟩
            (hf ⟨p.val, c.typeTwo_subset_rest p.property⟩)).mpr p.property⟩
  have hfInj := Books.choice_injective (coreSupports_disjoint c hK)
    (fun p T hT => trianglesOn_nonempty (corePages_subset_family c hK p hT)) hf
  have hgInj : Function.Injective (fun p : {T // T ∈ c.typeTwo} =>
      f ⟨p.val, c.typeTwo_subset_rest p.property⟩) := by
    intro p p' h
    exact Subtype.ext (congrArg (fun q : {T // T ∈ c.rest} => q.val) (hfInj h))
  have htype : (Books.choice f ∩ typeFamily c.remainingEdges c.old 2).card = c.typeTwo.card := by
    rw [heq, card_image_of_injective _ hgInj]
    simp
  exact c.rest_lexMaximum.of_same_counts hpack htype hcard

theorem coreEveryChoiceMeets {K : Finset (Finset (Sym2 V))}
    (hK : IsPacking c.specialFamily K) :
    Books.EveryChoiceMeets (trianglesOn c.remainingEdges) (corePages c K) := by
  intro f hf T hT
  obtain ⟨e, he⟩ := (coreChoices_lexMaximum c hK hf).meets_support hT (trianglesOn_nonempty hT)
  obtain ⟨U, hU, heU⟩ := mem_support.mp (mem_inter.mp he).2
  obtain ⟨p, rfl⟩ := Books.mem_choice.mp hU
  refine ⟨p, ?_⟩
  intro hd
  exact disjoint_left.mp hd (mem_inter.mp he).1 heU

theorem pairedRest_card {K : Finset (Finset (Sym2 V))}
    (hK : IsPacking c.specialFamily K) :
    (pairedRest c K).card = K.card := by
  classical
  have hex : ∀ q : {T // T ∈ K}, ∃ p : {T // T ∈ c.rest},
      q.val ∩ c.newEdges = p.val ∩ c.newEdges :=
    fun q => ThreeLayer.exists_parent (hK.1 q.property)
  choose par hpar using hex
  have hinj : Function.Injective (fun q : {T // T ∈ K} => (par q).val) := by
    intro q₁ q₂ heq
    have hpeq : par q₁ = par q₂ := Subtype.ext heq
    apply Subtype.ext
    apply hK.red_inter_injective c.specialFamily_colored q₁.property q₂.property
    exact (hpar q₁).trans (hpeq ▸ (hpar q₂).symm)
  have himg : univ.image (fun q : {T // T ∈ K} => (par q).val) = pairedRest c K := by
    ext p
    constructor
    · intro hp
      obtain ⟨q, _, rfl⟩ := mem_image.mp hp
      exact (mem_pairedRest c).mpr ⟨(par q).property, q.val, q.property, hpar q⟩
    · intro hp
      obtain ⟨hpR, q, hqK, hred⟩ := (mem_pairedRest c).mp hp
      have hpeq := ThreeLayer.owner_unique (hK.1 hqK) (par ⟨q, hqK⟩) ⟨p, hpR⟩ (hpar ⟨q, hqK⟩) hred
      exact mem_image.mpr ⟨⟨q, hqK⟩, mem_univ _, congrArg Subtype.val hpeq⟩
  rw [← himg, card_image_of_injective _ hinj]
  simp

/-- Base cover `C_0 := E(P' \ pairedRest K) ∪ R(pairedRest K)` in `G'`. -/
noncomputable def coreBase (K : Finset (Finset (Sym2 V))) : Finset (Sym2 V) :=
  support (c.rest \ pairedRest c K) ∪ redEdges c.newEdges (pairedRest c K)

theorem newEdges_subset_coreBase (K : Finset (Finset (Sym2 V))) :
    c.newEdges ⊆ coreBase c K := by
  intro e he
  obtain ⟨heSup, _⟩ := mem_sdiff.mp he
  obtain ⟨p, hpR, hep⟩ := mem_support.mp heSup
  by_cases hpPair : p ∈ pairedRest c K
  · exact mem_union_right _ (mem_redEdges.mpr ⟨mem_support.mpr ⟨p, hpPair, hep⟩, he⟩)
  · exact mem_union_left _ (mem_support.mpr ⟨p, mem_sdiff.mpr ⟨hpR, hpPair⟩, hep⟩)

theorem coreBase_card_le {K : Finset (Finset (Sym2 V))}
    (hK : IsPacking c.specialFamily K) :
    (coreBase c K).card + 2 * K.card ≤ 3 * c.rest.card := by
  have hsubRest : pairedRest c K ⊆ c.rest := pairedRest_subset_rest c K
  have hsubB : pairedRest c K ⊆ c.typeTwo := pairedRest_subset_typeTwo c hK
  have hcardP : (pairedRest c K).card = K.card := pairedRest_card c hK
  have hunpPack : IsPacking (trianglesOn c.remainingEdges) (c.rest \ pairedRest c K) :=
    c.rest_packing.subfamily sdiff_subset
  have hunpSup : (support (c.rest \ pairedRest c K)).card =
      3 * (c.rest \ pairedRest c K).card :=
    hunpPack.card_support_uniform (fun _ hT => trianglesOn_card (hunpPack.1 hT))
  have hpairPack : IsPacking (typeFamily c.remainingEdges c.old 2) (pairedRest c K) :=
    c.typeTwo_maximum.1.subfamily hsubB
  have hredEq : redEdges c.newEdges (pairedRest c K) =
      redEdges (c.remainingEdges \ c.old) (pairedRest c K) := by
    ext e
    simp only [mem_redEdges]
    constructor
    · rintro ⟨heSup, heNew⟩
      exact ⟨heSup, mem_sdiff.mpr ⟨c.newEdges_subset_remaining heNew, (mem_sdiff.mp heNew).2⟩⟩
    · rintro ⟨heSup, heRemOld⟩
      exact ⟨heSup, mem_sdiff.mpr ⟨support_mono hsubRest heSup, (mem_sdiff.mp heRemOld).2⟩⟩
  have hredCard : (redEdges c.newEdges (pairedRest c K)).card = (pairedRest c K).card := by
    rw [hredEq]
    exact hpairPack.card_redEdges (typeTwo_colored c.remainingEdges c.old)
  have hsplit := card_sdiff_add_card_eq_card hsubRest
  have hunion := card_union_le (support (c.rest \ pairedRest c K))
    (redEdges c.newEdges (pairedRest c K))
  change (support (c.rest \ pairedRest c K) ∪ redEdges c.newEdges (pairedRest c K)).card +
    2 * K.card ≤ 3 * c.rest.card
  omega

/-- Opposite edges `{w_k x_k : k ∈ B_out}` added for sink books `B_out = helperRoots c hQ`. -/
noncomputable def oppOutEdges {Q : Finset (Finset (Sym2 V))}
    (hQ : IsPacking c.specialFamily Q) : Finset (Sym2 V) :=
  (HelperArborescence.helperRoots c hQ).biUnion
    (fun k => ((TwoLayer.book c hQ k).opposite).toFinset)

theorem oppOutEdges_card_le {Q : Finset (Finset (Sym2 V))}
    (hQ : IsPacking c.specialFamily Q) :
    (oppOutEdges c hQ).card ≤ (HelperArborescence.helperRoots c hQ).card := by
  calc
    (oppOutEdges c hQ).card ≤
        ∑ k ∈ HelperArborescence.helperRoots c hQ,
          (((TwoLayer.book c hQ k).opposite).toFinset).card := card_biUnion_le
    _ ≤ ∑ _k ∈ HelperArborescence.helperRoots c hQ, 1 := by
      apply sum_le_sum
      intro k _
      cases (TwoLayer.book c hQ k).opposite <;> simp
    _ = (HelperArborescence.helperRoots c hQ).card := by simp

/-- Remaining-graph core cover `D_core := C_0(K) ∪ oppOutEdges`. -/
noncomputable def remainingCoreCover {Q : Finset (Finset (Sym2 V))}
    (hQ : IsPacking c.specialFamily Q) : Finset (Sym2 V) :=
  coreBase c (activePages c hQ) ∪ oppOutEdges c hQ

theorem remainingCoreCover_card_le {Q : Finset (Finset (Sym2 V))}
    (hQ : IsPacking c.specialFamily Q) :
    (remainingCoreCover c hQ).card + 2 * Q.card ≤
      3 * c.rest.card + (HelperArborescence.helperRoots c hQ).card +
        2 * (privZeroPages c hQ).card := by
  have hbase := coreBase_card_le c (activePages_packing c hQ)
  have hopp := oppOutEdges_card_le c hQ
  have hact := activePages_add_privZeroPages_card c hQ
  have hunion := card_union_le (coreBase c (activePages c hQ)) (oppOutEdges c hQ)
  change (coreBase c (activePages c hQ) ∪ oppOutEdges c hQ).card + 2 * Q.card ≤ _
  omega

end CoreBooks

section GeometryHelpers

variable {Q : Finset (Finset (Sym2 V))} (hQ : IsPacking c.specialFamily Q)

omit [Fintype V] in
theorem triangleEdges_swap_first (a b w : V) :
    triangleEdges b a w = triangleEdges a b w := by
  ext e
  simp only [mem_triangleEdges, Sym2.eq_swap]
  tauto

/-- For `Z = triangleEdges u v z ∈ c.specialFamily` with `s(u, v) ∈ c.newEdges` and
`p ∈ c.rest` containing `s(u, v)`, the two blue edges `s(u, z), s(v, z)` lie in
`c.oldRemaining \ support c.rest` and `Z` is disjoint from `support (c.rest.erase p)`. -/
theorem special_triangle_blue_and_disjoint {u v z : V} {p : Finset (Sym2 V)}
    (hZ : triangleEdges u v z ∈ c.specialFamily)
    (hpR : p ∈ c.rest) (hep : s(u, v) ∈ p) (huvN : s(u, v) ∈ c.newEdges)
    (huz : u ≠ z) (hvz : v ≠ z) :
    s(u, z) ∈ c.oldRemaining \ support c.rest ∧
    s(v, z) ∈ c.oldRemaining \ support c.rest ∧
    Disjoint (triangleEdges u v z) (support (c.rest.erase p)) := by
  have hredEq : triangleEdges u v z ∩ c.newEdges = {s(u, v)} :=
    c.specialFamily_colored.red_eq_singleton hZ (by simp) huvN
  have hblueMem {a : V} (ha : s(a, z) ∈ triangleEdges u v z)
      (hne : s(a, z) ≠ s(u, v)) : s(a, z) ∈ c.oldRemaining \ support c.rest := by
    have hmem := (mem_oneRedTriangles.mp hZ).2.1 ha
    rcases mem_union.mp hmem with hN | hB
    · have heq : s(a, z) = s(u, v) :=
        mem_singleton.mp (hredEq ▸ mem_inter.mpr ⟨ha, hN⟩)
      exact (hne heq).elim
    · exact hB
  have huzNe : s(u, z) ≠ s(u, v) := by
    intro h
    have hvz' : z = v := Sym2.congr_right.mp h
    exact hvz hvz'.symm
  have hvzNe : s(v, z) ≠ s(u, v) := by
    intro h
    rw [Sym2.eq_swap] at h
    have huz' : z = u := Sym2.congr_left.mp h
    exact huz huz'.symm
  have huzB := hblueMem (by simp) huzNe
  have hvzB := hblueMem (by simp) hvzNe
  refine ⟨huzB, hvzB, disjoint_left.mpr ?_⟩
  intro e heZ heSup
  obtain ⟨p', hp'E, hep'⟩ := mem_support.mp heSup
  obtain ⟨hp'ne, hp'R⟩ := mem_erase.mp hp'E
  rcases mem_triangleEdges.mp heZ with rfl | rfl | rfl
  · exact disjoint_left.mp (c.rest_packing.2 hpR hp'R hp'ne.symm) hep hep'
  · exact (mem_sdiff.mp huzB).2 (mem_support.mpr ⟨p', hp'R, hep'⟩)
  · exact (mem_sdiff.mp hvzB).2 (mem_support.mpr ⟨p', hp'R, hep'⟩)

/-- Canonical geometry of a paired two-page book `(p, q)` with `p ∈ c.rest`, `q ∈ Q`, and
`q ∩ c.newEdges = p ∩ c.newEdges`: extracts `i : {T // T ∈ c.typeTwo}` (`i.val = p`) and
4 distinct vertices `[u, v, w, x].Nodup` with `p = triangleEdges u v w`, `q = triangleEdges u v x`,
`(TwoLayer.book c hQ i).spine = s(u, v) ∈ c.newEdges`, `(TwoLayer.book c hQ i).pages = {p, q}`,
and `(TwoLayer.book c hQ i).opposite = some s(w, x)`. -/
theorem paired_book_geometry {p q : Finset (Sym2 V)}
    (hpR : p ∈ c.rest) (hqQ : q ∈ Q) (hred : q ∩ c.newEdges = p ∩ c.newEdges) :
    ∃ (i : {T // T ∈ c.typeTwo}) (u v w x : V),
      i.val = p ∧ [u, v, w, x].Nodup ∧
      p = triangleEdges u v w ∧ q = triangleEdges u v x ∧
      (TwoLayer.book c hQ i).spine = s(u, v) ∧ s(u, v) ∈ c.newEdges ∧
      (TwoLayer.book c hQ i).pages = {p, q} ∧
      (TwoLayer.book c hQ i).opposite = some s(w, x) := by
  have hqS : q ∈ c.specialFamily := hQ.1 hqQ
  have hpB : p ∈ c.typeTwo := by
    apply (ThreeLayer.parent_typeTwo_iff_red_nonempty ⟨p, hpR⟩).mpr
    rw [← hred]
    exact card_pos.mp (by rw [(c.specialFamily_colored q hqS).2]; decide)
  let i : {T // T ∈ c.typeTwo} := ⟨p, hpB⟩
  let sp := (TwoLayer.book c hQ i).spine
  obtain ⟨u, v, hspUV⟩ : ∃ u v, sp = s(u, v) :=
    Sym2.inductionOn sp (fun u v => ⟨u, v, rfl⟩)
  have hspMemP : s(u, v) ∈ p ∩ c.newEdges := by
    rw [← hspUV]
    change (TwoLayer.book c hQ i).spine ∈ p ∩ c.newEdges
    rw [TwoLayer.book_spine]
    exact Construction.typeTwoSpine_mem i
  have hspMemQ : s(u, v) ∈ q ∩ c.newEdges := hred.symm ▸ hspMemP
  have hpTri : IsTriangle p := (mem_trianglesOn.mp (c.rest_packing.1 hpR)).1
  have hqTri : IsTriangle q := (mem_oneRedTriangles.mp hqS).1
  have huv : u ≠ v := hpTri.ne_of_mem (mem_inter.mp hspMemP).1
  obtain ⟨w, huw, hvw, hpw⟩ := hpTri.exists_third_of_mem (mem_inter.mp hspMemP).1
  obtain ⟨x, hux, hvx, hqx⟩ := hqTri.exists_third_of_mem (mem_inter.mp hspMemQ).1
  have hpNeQ : p ≠ q := fun heq => ThreeLayer.special_not_rest hqS (heq ▸ hpR)
  have hwx : w ≠ x := by
    rintro rfl
    exact hpNeQ (hpw.trans hqx.symm)
  have hnodup : [u, v, w, x].Nodup := by
    simp [List.nodup_cons, huv, huw, hux, hvw, hvx, hwx]
  have hredRem : q ∩ (c.remainingEdges \ c.old) = p ∩ (c.remainingEdges \ c.old) := by
    have hqEq : q ∩ (c.remainingEdges \ c.old) = q ∩ c.newEdges := by
      ext e
      constructor
      · intro he
        obtain ⟨heq, heRO⟩ := mem_inter.mp he
        obtain ⟨_, heNotOld⟩ := mem_sdiff.mp heRO
        refine mem_inter.mpr ⟨heq, ?_⟩
        rcases mem_union.mp ((mem_oneRedTriangles.mp hqS).2.1 heq) with hN | hB
        · exact hN
        · exact (heNotOld (mem_sdiff.mp (mem_sdiff.mp hB).1).1).elim
      · intro he
        obtain ⟨heq, heN⟩ := mem_inter.mp he
        exact mem_inter.mpr ⟨heq,
          mem_sdiff.mpr ⟨c.newEdges_subset_remaining heN, (mem_sdiff.mp heN).2⟩⟩
    have hpEq : p ∩ (c.remainingEdges \ c.old) = p ∩ c.newEdges := by
      ext e
      constructor
      · intro he
        obtain ⟨hep, heRO⟩ := mem_inter.mp he
        obtain ⟨_, heNotOld⟩ := mem_sdiff.mp heRO
        exact mem_inter.mpr ⟨hep,
          mem_sdiff.mpr ⟨mem_support.mpr ⟨p, hpR, hep⟩, heNotOld⟩⟩
      · intro he
        obtain ⟨hep, heN⟩ := mem_inter.mp he
        exact mem_inter.mpr ⟨hep, mem_sdiff.mpr
          ⟨(mem_trianglesOn.mp (c.rest_packing.1 hpR)).2 hep, (mem_sdiff.mp heN).2⟩⟩
    rw [hqEq, hpEq, hred]
  have hpages : (TwoLayer.book c hQ i).pages = {p, q} := by
    rw [TwoLayer.book_pages]
    exact Layered.pages_eq_pair (typeTwo_colored c.remainingEdges c.old)
      (TwoLayer.residual_packing c hQ) i hqQ hredRem
  have hopp : (TwoLayer.book c hQ i).opposite = some s(w, x) := by
    have hcard2 : (TwoLayer.book c hQ i).pages.card = 2 := by
      rw [hpages, card_pair hpNeQ]
    have hspEq : (TwoLayer.book c hQ i).spine = s(u, v) := hspUV
    cases hb : TwoLayer.book c hQ i with
    | single a b y hv =>
      rw [hb] at hcard2
      simp [Book.pages] at hcard2
    | triple a b y₁ y₂ y₃ hv =>
      rw [hb, Book.pages_card] at hcard2
      simp [Book.pageCount] at hcard2
    | double a b y₁ y₂ hv =>
      rw [hb] at hpages hspEq
      dsimp [Book.spine] at hspEq
      dsimp [Book.pages] at hpages
      have htriSwap : ∀ z, triangleEdges a b z = triangleEdges u v z := by
        intro z
        rcases Sym2.eq_iff.mp hspEq with ⟨ha, hb'⟩ | ⟨ha, hb'⟩
        · rw [ha, hb']
        · rw [ha, hb']
          exact triangleEdges_swap_first u v z
      rw [htriSwap y₁, htriSwap y₂, hpw, hqx] at hpages
      have hthirdEq : ∀ {z₁ z₂ : V}, u ≠ z₁ → v ≠ z₁ →
          triangleEdges u v z₁ = triangleEdges u v z₂ → z₁ = z₂ := by
        intro z₁ z₂ huz₁ hvz₁ heqT
        have hm : s(u, z₁) ∈ triangleEdges u v z₂ := heqT ▸ (by simp)
        simp only [mem_triangleEdges, Sym2.eq_iff] at hm
        rcases hm with (⟨_, hz⟩ | ⟨hu1, _⟩) | (⟨_, hz⟩ | ⟨_, hz⟩) | (⟨hu1, _⟩ | ⟨_, hz⟩)
        · exact (hvz₁ hz.symm).elim
        · exact (huv hu1).elim
        · exact hz
        · exact (huz₁ hz.symm).elim
        · exact (huv hu1).elim
        · exact (hvz₁ hz.symm).elim
      have hvy : a ≠ b ∧ a ≠ y₁ ∧ a ≠ y₂ ∧ b ≠ y₁ ∧ b ≠ y₂ ∧ y₁ ≠ y₂ := by
        simpa [List.nodup_cons, and_assoc] using hv
      have huy₁ : u ≠ y₁ ∧ v ≠ y₁ ∧ u ≠ y₂ ∧ v ≠ y₂ := by
        rcases Sym2.eq_iff.mp hspEq with ⟨ha, hb'⟩ | ⟨ha, hb'⟩
        · rw [← ha, ← hb']
          exact ⟨hvy.2.1, hvy.2.2.2.1, hvy.2.2.1, hvy.2.2.2.2.1⟩
        · rw [← hb', ← ha]
          exact ⟨hvy.2.2.2.1, hvy.2.1, hvy.2.2.2.2.1, hvy.2.2.1⟩
      have hy₁Mem : triangleEdges u v y₁ ∈
          ({triangleEdges u v w, triangleEdges u v x} : Finset (Finset (Sym2 V))) :=
        hpages ▸ (by simp)
      have hy₂Mem : triangleEdges u v y₂ ∈
          ({triangleEdges u v w, triangleEdges u v x} : Finset (Finset (Sym2 V))) :=
        hpages ▸ (by simp)
      simp only [mem_insert, mem_singleton] at hy₁Mem hy₂Mem
      simp only [Book.opposite, Option.some.injEq]
      rcases hy₁Mem with h1w | h1x <;> rcases hy₂Mem with h2w | h2x
      · have := (hthirdEq huy₁.1 huy₁.2.1 h1w).trans (hthirdEq huy₁.2.2.1 huy₁.2.2.2 h2w).symm
        exact (hvy.2.2.2.2.2 this).elim
      · rw [hthirdEq huy₁.1 huy₁.2.1 h1w, hthirdEq huy₁.2.2.1 huy₁.2.2.2 h2x]
      · rw [hthirdEq huy₁.1 huy₁.2.1 h1x, hthirdEq huy₁.2.2.1 huy₁.2.2.2 h2w, Sym2.eq_swap]
      · have := (hthirdEq huy₁.1 huy₁.2.1 h1x).trans (hthirdEq huy₁.2.2.1 huy₁.2.2.2 h2x).symm
        exact (hvy.2.2.2.2.2 this).elim
  exact ⟨i, u, v, w, x, rfl, hnodup, hpw, hqx, hspUV, (mem_inter.mp hspMemP).2, hpages, hopp⟩

/-- Every non-private page `q = triangleEdges u v x ∈ Q \ privPages c Q` paired with
`p = triangleEdges u v w ∈ c.rest` admits a second page `Z = triangleEdges u v z ∈ c.specialFamily`
on 5 distinct vertices `[u, v, w, x, z].Nodup`. -/
theorem nonprivate_third_vertex {u v w x : V}
    (hnodup : [u, v, w, x].Nodup)
    (hpR : triangleEdges u v w ∈ c.rest)
    (hqQ : triangleEdges u v x ∈ Q)
    (hspN : s(u, v) ∈ c.newEdges)
    (hnp : triangleEdges u v x ∉ privPages c Q) :
    ∃ z : V, [u, v, w, x, z].Nodup ∧
      triangleEdges u v z ∈ c.specialFamily ∧
      triangleEdges u v z ≠ triangleEdges u v x := by
  have hex : ∃ Z ∈ c.specialFamily,
      Z ∩ c.newEdges = triangleEdges u v x ∩ c.newEdges ∧ Z ≠ triangleEdges u v x := by
    by_contra hall
    push Not at hall
    exact hnp (mem_privateRedPages.mpr ⟨hqQ, hall⟩)
  obtain ⟨Z, hZS, hZred, hZneQ⟩ := hex
  have huvQ : s(u, v) ∈ triangleEdges u v x ∩ c.newEdges := mem_inter.mpr ⟨by simp, hspN⟩
  have huvZ : s(u, v) ∈ Z := (mem_inter.mp (hZred.symm ▸ huvQ)).1
  have hZtri : IsTriangle Z := (mem_oneRedTriangles.mp hZS).1
  obtain ⟨z, huz, hvz, rfl⟩ := hZtri.exists_third_of_mem huvZ
  have hzx : x ≠ z := by
    rintro rfl
    exact hZneQ rfl
  have hzw : w ≠ z := by
    rintro rfl
    exact ThreeLayer.special_not_rest hZS hpR
  have hnd4 : u ≠ v ∧ u ≠ w ∧ u ≠ x ∧ v ≠ w ∧ v ≠ x ∧ w ≠ x := by
    simpa [List.nodup_cons, and_assoc] using hnodup
  refine ⟨z, ?_, hZS, hZneQ⟩
  simp [List.nodup_cons, hnd4.1, hnd4.2.1, hnd4.2.2.1, huz,
    hnd4.2.2.2.1, hnd4.2.2.2.2.1, hvz, hnd4.2.2.2.2.2, hzw, hzx]

include hQ in
/-- When `s(w, x) ∈ c.oldRemaining`, both `triangleEdges α w x` (`α ∈ {u, v}`) belong to
`trianglesOn c.remainingEdges` with all three edges in `c.oldRemaining`. -/
theorem blue_candidate_in_remaining {u v w x α : V}
    (hnodup : [u, v, w, x].Nodup)
    (hpR : triangleEdges u v w ∈ c.rest)
    (hqQ : triangleEdges u v x ∈ Q)
    (hspN : s(u, v) ∈ c.newEdges)
    (hfOld : s(w, x) ∈ c.oldRemaining)
    (hα : α = u ∨ α = v) :
    triangleEdges α w x ∈ trianglesOn c.remainingEdges ∧
    triangleEdges α w x ⊆ c.oldRemaining ∧
    (triangleEdges α w x).Nonempty := by
  have hnd : u ≠ v ∧ u ≠ w ∧ u ≠ x ∧ v ≠ w ∧ v ≠ x ∧ w ≠ x := by
    simpa [List.nodup_cons, and_assoc] using hnodup
  have hαw : α ≠ w := by rcases hα with rfl | rfl; exacts [hnd.2.1, hnd.2.2.2.1]
  have hαx : α ≠ x := by rcases hα with rfl | rfl; exacts [hnd.2.2.1, hnd.2.2.2.2.1]
  have htri : IsTriangle (triangleEdges α w x) := isTriangle_triangleEdges hαw hαx hnd.2.2.2.2.2
  have hqB := special_triangle_blue_and_disjoint c (hQ.1 hqQ) hpR (by simp) hspN
    hnd.2.2.1 hnd.2.2.2.2.1
  have hαxOld : s(α, x) ∈ c.oldRemaining := by
    rcases hα with rfl | rfl
    · exact (mem_sdiff.mp hqB.1).1
    · exact (mem_sdiff.mp hqB.2.1).1
  have hpTri : triangleEdges u v w ∈ trianglesOn c.remainingEdges := c.rest_packing.1 hpR
  have hαwMem : s(α, w) ∈ triangleEdges u v w := by rcases hα with rfl | rfl <;> simp
  have hαwNe : s(α, w) ≠ s(u, v) := by
    intro heq
    rcases hα with rfl | rfl
    · exact hnd.2.2.2.1 (Sym2.congr_right.mp heq).symm
    · rw [Sym2.eq_swap] at heq
      exact hnd.2.1 (Sym2.congr_left.mp heq).symm
  have hαwOld : s(α, w) ∈ c.oldRemaining := by
    have hαwRem : s(α, w) ∈ c.remainingEdges := (mem_trianglesOn.mp hpTri).2 hαwMem
    have hαwInOld : s(α, w) ∈ c.old := by
      by_contra hnOld
      have hcard1 := c.remaining_new_le_one hpTri
      have heq := card_le_one.mp hcard1 s(α, w) (mem_sdiff.mpr ⟨hαwMem, hnOld⟩)
        s(u, v) (mem_sdiff.mpr ⟨by simp, (mem_sdiff.mp hspN).2⟩)
      exact hαwNe heq
    exact mem_sdiff.mpr ⟨hαwInOld, (mem_sdiff.mp hαwRem).2⟩
  have hsubOld : triangleEdges α w x ⊆ c.oldRemaining := by
    intro e he
    rcases mem_triangleEdges.mp he with rfl | rfl | rfl
    · exact hαwOld
    · exact hαxOld
    · exact hfOld
  exact ⟨mem_trianglesOn.mpr ⟨htri, hsubOld.trans c.oldRemaining_subset_remaining⟩,
    hsubOld, ⟨s(w, x), by simp⟩⟩

include hQ in
/-- Step 3 Obstruction (`k ∈ I_np \ {i}`): Zero non-private 2-cycles, chains, or `Q_1`-stars. -/
theorem step3_nonprivate_obstruction
    {ui vi wi xi zi uk vk wk xk zk : V}
    (hvi5 : [ui, vi, wi, xi, zi].Nodup)
    (hvk5 : [uk, vk, wk, xk, zk].Nodup)
    (hTi : triangleEdges ui vi wi ∈ c.typeTwo)
    (hQi : triangleEdges ui vi xi ∈ Q)
    (hZi : triangleEdges ui vi zi ∈ c.specialFamily)
    (he_i : s(ui, vi) ∈ c.newEdges)
    (hTk : triangleEdges uk vk wk ∈ c.typeTwo)
    (hQk : triangleEdges uk vk xk ∈ Q)
    (hZk : triangleEdges uk vk zk ∈ c.specialFamily)
    (he_k : s(uk, vk) ∈ c.newEdges)
    (hneT : triangleEdges ui vi wi ≠ triangleEdges uk vk wk)
    (hf_eq : s(wi, xi) = s(uk, wk)) : False := by
  let Ti := triangleEdges ui vi wi
  let Qi := triangleEdges ui vi xi
  let Zi := triangleEdges ui vi zi
  let Tk := triangleEdges uk vk wk
  let Qk := triangleEdges uk vk xk
  let Zk := triangleEdges uk vk zk
  let P₀ := (c.rest.erase Ti).erase Tk
  have hTiR : Ti ∈ c.rest := c.typeTwo_subset_rest hTi
  have hTkR : Tk ∈ c.rest := c.typeTwo_subset_rest hTk
  have hneSp : s(ui, vi) ≠ s(uk, vk) := by
    intro hspEq
    have hm1 : s(ui, vi) ∈ Ti := by simp [Ti]
    have hm2 : s(ui, vi) ∈ Tk := by rw [hspEq]; simp [Tk]
    exact disjoint_left.mp (c.rest_packing.2 hTiR hTkR hneT) hm1 hm2
  have hneQ : Qi ≠ Qk := by
    intro heq
    have h1 : Qi ∩ c.newEdges = {s(ui, vi)} :=
      c.specialFamily_colored.red_eq_singleton (hQ.1 hQi) (by simp [Qi]) he_i
    have h2 : Qk ∩ c.newEdges = {s(uk, vk)} :=
      c.specialFamily_colored.red_eq_singleton (hQ.1 hQk) (by simp [Qk]) he_k
    have hspEq : s(ui, vi) = s(uk, vk) :=
      singleton_injective (h1.symm.trans ((congrArg (· ∩ c.newEdges) heq).trans h2))
    exact hneSp hspEq
  have hndI5 : ui ≠ vi ∧ ui ≠ wi ∧ ui ≠ xi ∧ ui ≠ zi ∧ vi ≠ wi ∧ vi ≠ xi ∧ vi ≠ zi ∧
      wi ≠ xi ∧ wi ≠ zi ∧ xi ≠ zi := by simpa [List.nodup_cons, and_assoc] using hvi5
  have hndK5 : uk ≠ vk ∧ uk ≠ wk ∧ uk ≠ xk ∧ uk ≠ zk ∧ vk ≠ wk ∧ vk ≠ xk ∧ vk ≠ zk ∧
      wk ≠ xk ∧ wk ≠ zk ∧ xk ≠ zk := by simpa [List.nodup_cons, and_assoc] using hvk5
  have hvi4 : [ui, vi, wi, xi].Nodup := by
    simp [List.nodup_cons, hndI5.1, hndI5.2.1, hndI5.2.2.1, hndI5.2.2.2.2.1,
      hndI5.2.2.2.2.2.1, hndI5.2.2.2.2.2.2.2.1]
  have hvk4 : [uk, vk, wk, xk].Nodup := by
    simp [List.nodup_cons, hndK5.1, hndK5.2.1, hndK5.2.2.1, hndK5.2.2.2.2.1,
      hndK5.2.2.2.2.2.1, hndK5.2.2.2.2.2.2.2.1]
  have hfOld : s(wi, xi) ∈ c.oldRemaining := by
    rw [hf_eq]
    have hTkTri : Tk ∈ trianglesOn c.remainingEdges := c.rest_packing.1 hTkR
    have hneSpK : s(uk, wk) ≠ s(uk, vk) := fun h => hndK5.2.2.2.2.1 (Sym2.congr_right.mp h).symm
    have hRem : s(uk, wk) ∈ c.remainingEdges := (mem_trianglesOn.mp hTkTri).2 (by simp [Tk])
    have hInOld : s(uk, wk) ∈ c.old := by
      by_contra hnOld
      have heq := card_le_one.mp (c.remaining_new_le_one hTkTri)
        s(uk, wk) (mem_sdiff.mpr ⟨by simp [Tk], hnOld⟩)
        s(uk, vk) (mem_sdiff.mpr ⟨by simp [Tk], (mem_sdiff.mp he_k).2⟩)
      exact hneSpK heq
    exact mem_sdiff.mpr ⟨hInOld, (mem_sdiff.mp hRem).2⟩

  have hZiD := special_triangle_blue_and_disjoint c hZi hTiR (by simp [Ti]) he_i
    hndI5.2.2.2.1 hndI5.2.2.2.2.2.2.1
  have hQiD := special_triangle_blue_and_disjoint c (hQ.1 hQi) hTiR (by simp [Ti]) he_i
    hndI5.2.2.1 hndI5.2.2.2.2.2.1
  have hQkD := special_triangle_blue_and_disjoint c (hQ.1 hQk) hTkR (by simp [Tk]) he_k
    hndK5.2.2.1 hndK5.2.2.2.2.2.1
  have hZkD := special_triangle_blue_and_disjoint c hZk hTkR (by simp [Tk]) he_k
    hndK5.2.2.2.1 hndK5.2.2.2.2.2.2.1

  have hZiP₀ : Disjoint Zi (support P₀) :=
    hZiD.2.2.mono_right (support_mono (erase_subset Tk _))
  have hQkP₀ : Disjoint Qk (support P₀) := by
    have heraseSwap : P₀ ⊆ c.rest.erase Tk := by
      intro X hX
      obtain ⟨hneK, hXi⟩ := mem_erase.mp hX
      exact mem_erase.mpr ⟨hneK, (mem_erase.mp hXi).2⟩
    exact hQkD.2.2.mono_right (support_mono heraseSwap)
  have hZkP₀ : Disjoint Zk (support P₀) := by
    have heraseSwap : P₀ ⊆ c.rest.erase Tk := by
      intro X hX
      obtain ⟨hneK, hXi⟩ := mem_erase.mp hX
      exact mem_erase.mpr ⟨hneK, (mem_erase.mp hXi).2⟩
    exact hZkD.2.2.mono_right (support_mono heraseSwap)

  have hUP₀ : ∀ α, (α = ui ∨ α = vi) → Disjoint (triangleEdges α wi xi) (support P₀) := by
    intro α hα
    apply disjoint_left.mpr
    intro e heU heSup
    obtain ⟨X, hXP₀, heX⟩ := mem_support.mp heSup
    obtain ⟨hXneK, hX1⟩ := mem_erase.mp hXP₀
    obtain ⟨hXneI, hXR⟩ := mem_erase.mp hX1
    rcases mem_triangleEdges.mp heU with rfl | rfl | rfl
    · have hmTi : s(α, wi) ∈ Ti := by rcases hα with rfl | rfl <;> simp [Ti]
      exact disjoint_left.mp (c.rest_packing.2 hTiR hXR hXneI.symm) hmTi heX
    · have hmQi : s(α, xi) ∉ support c.rest := by
        rcases hα with rfl | rfl
        · exact (mem_sdiff.mp hQiD.1).2
        · exact (mem_sdiff.mp hQiD.2.1).2
      exact hmQi (mem_support.mpr ⟨X, hXR, heX⟩)
    · rw [hf_eq] at heX
      exact disjoint_left.mp (c.rest_packing.2 hTkR hXR hXneK.symm) (by simp [Tk]) heX

  have hdUZi_u : Disjoint (triangleEdges ui wi xi) Zi := by
    have h5' : [ui, wi, xi, vi, zi].Nodup := by
      have h : ui ≠ vi ∧ ui ≠ wi ∧ ui ≠ xi ∧ ui ≠ zi ∧ vi ≠ wi ∧ vi ≠ xi ∧ vi ≠ zi ∧
          wi ≠ xi ∧ wi ≠ zi ∧ xi ≠ zi := by simpa [List.nodup_cons, and_assoc] using hvi5
      simp [List.nodup_cons, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1.symm,
        h.2.2.2.2.2.1.symm, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1,
        h.2.2.2.2.2.2.2.2.2]
    exact triangleEdges_disjoint_of_five_distinct h5'

  have hdUZi_v : Disjoint (triangleEdges vi wi xi) Zi := by
    have h5' : [vi, wi, xi, ui, zi].Nodup := by
      simp [List.nodup_cons, hndI5.1.symm, hndI5.2.1.symm, hndI5.2.2.1.symm, hndI5.2.2.2.1,
        hndI5.2.2.2.2.1, hndI5.2.2.2.2.2.1, hndI5.2.2.2.2.2.2.1, hndI5.2.2.2.2.2.2.2.1,
        hndI5.2.2.2.2.2.2.2.2.1, hndI5.2.2.2.2.2.2.2.2.2]
    have hd := triangleEdges_disjoint_of_five_distinct h5'
    change Disjoint (triangleEdges vi wi xi) (triangleEdges ui vi zi)
    rwa [triangleEdges_swap_first ui vi zi] at hd

  have hUu := blue_candidate_in_remaining c hQ hvi4 hTiR hQi he_i hfOld (Or.inl rfl)
  have hUv := blue_candidate_in_remaining c hQ hvi4 hTiR hQi he_i hfOld (Or.inr rfl)

  -- Step 3a: ¬ Disjoint Zi Qk via 2-for-3 exchange on (Ti, Tk, Zi, Qk, U_i^(u))
  have hdUuQk : Disjoint (triangleEdges ui wi xi) Qk := by
    apply disjoint_left.mpr
    intro e heU heQk
    rcases mem_triangleEdges.mp heQk with rfl | rfl | rfl
    · exact (mem_sdiff.mp he_k).2 (mem_sdiff.mp (hUu.2.1 heU)).1
    · rcases mem_triangleEdges.mp heU with heq | heq | heq
      · have hm : s(uk, xk) ∈ Ti := by rw [heq]; dsimp [Ti]; simp
        exact (mem_sdiff.mp hQkD.1).2 (mem_support.mpr ⟨Ti, hTiR, hm⟩)
      · have hm1 : s(uk, xk) ∈ Qi := by rw [heq]; dsimp [Qi]; simp
        have hm2 : s(uk, xk) ∈ Qk := by dsimp [Qk]; simp
        exact disjoint_left.mp (hQ.2 hQi hQk hneQ) hm1 hm2
      · have hm : s(uk, xk) ∈ Tk := by rw [heq, hf_eq]; dsimp [Tk]; simp
        exact (mem_sdiff.mp hQkD.1).2 (mem_support.mpr ⟨Tk, hTkR, hm⟩)
    · rcases mem_triangleEdges.mp heU with heq | heq | heq
      · have hm : s(vk, xk) ∈ Ti := by rw [heq]; dsimp [Ti]; simp
        exact (mem_sdiff.mp hQkD.2.1).2 (mem_support.mpr ⟨Ti, hTiR, hm⟩)
      · have hm1 : s(vk, xk) ∈ Qi := by rw [heq]; dsimp [Qi]; simp
        have hm2 : s(vk, xk) ∈ Qk := by dsimp [Qk]; simp
        exact disjoint_left.mp (hQ.2 hQi hQk hneQ) hm1 hm2
      · have hm : s(vk, xk) ∈ Tk := by rw [heq, hf_eq]; dsimp [Tk]; simp
        exact (mem_sdiff.mp hQkD.2.1).2 (mem_support.mpr ⟨Tk, hTkR, hm⟩)

  have hnotDisZiQk : ¬ Disjoint Zi Qk := by
    intro hdZiQk
    exact c.rest_lexMaximum.no_two_to_three (typeFamily_subset _ _ _)
      hTi hTk hneT
      (c.specialFamily_subset_typeTwo hZi) (c.specialFamily_subset_typeTwo (hQ.1 hQk)) hUu.1
      ⟨s(ui, vi), by simp⟩ ⟨s(uk, vk), by simp⟩ hUu.2.2
      hdZiQk hdUZi_u hdUuQk hZiP₀ hQkP₀ (hUP₀ ui (Or.inl rfl))

  -- Step 3b: Choose α ∈ {ui, vi} with Disjoint (U_i^(α)) Zk, forcing ¬ Disjoint Zi Zk
  have hexAlpha : s(ui, xi) ∉ ({s(uk, zk), s(vk, zk)} : Finset (Sym2 V)) ∨
      s(vi, xi) ∉ ({s(uk, zk), s(vk, zk)} : Finset (Sym2 V)) := by
    by_contra hboth
    push Not at hboth
    obtain ⟨hmU, hmV⟩ := hboth
    have huiNeVi : ui ≠ vi := hndI5.1
    simp only [mem_insert, mem_singleton, Sym2.eq_iff] at hmU hmV
    rcases hmU with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
      rcases hmV with (⟨h1, h2⟩ | ⟨h1, h2⟩) | (⟨h1, h2⟩ | ⟨h1, h2⟩) <;>
      simp_all [Sym2.eq_swap]

  have hnotDisZiZk : ¬ Disjoint Zi Zk := by
    intro hdZiZk
    rcases hexAlpha with hnotU | hnotV
    · have hdUuZk : Disjoint (triangleEdges ui wi xi) Zk := by
        apply disjoint_left.mpr
        intro e heU heZk
        rcases mem_triangleEdges.mp heZk with rfl | rfl | rfl
        · exact (mem_sdiff.mp he_k).2 (mem_sdiff.mp (hUu.2.1 heU)).1
        · rcases mem_triangleEdges.mp heU with heq | heq | heq
          · have hm : s(uk, zk) ∈ Ti := by rw [heq]; dsimp [Ti]; simp
            exact (mem_sdiff.mp hZkD.1).2 (mem_support.mpr ⟨Ti, hTiR, hm⟩)
          · exact hnotU (by simp [heq])
          · have hm : s(uk, zk) ∈ Tk := by rw [heq, hf_eq]; dsimp [Tk]; simp
            exact (mem_sdiff.mp hZkD.1).2 (mem_support.mpr ⟨Tk, hTkR, hm⟩)
        · rcases mem_triangleEdges.mp heU with heq | heq | heq
          · have hm : s(vk, zk) ∈ Ti := by rw [heq]; dsimp [Ti]; simp
            exact (mem_sdiff.mp hZkD.2.1).2 (mem_support.mpr ⟨Ti, hTiR, hm⟩)
          · exact hnotU (by simp [heq])
          · have hm : s(vk, zk) ∈ Tk := by rw [heq, hf_eq]; dsimp [Tk]; simp
            exact (mem_sdiff.mp hZkD.2.1).2 (mem_support.mpr ⟨Tk, hTkR, hm⟩)
      exact c.rest_lexMaximum.no_two_to_three (typeFamily_subset _ _ _)
        hTi hTk hneT
        (c.specialFamily_subset_typeTwo hZi) (c.specialFamily_subset_typeTwo hZk) hUu.1
        ⟨s(ui, vi), by simp⟩ ⟨s(uk, vk), by simp⟩ hUu.2.2
        hdZiZk hdUZi_u hdUuZk hZiP₀ hZkP₀ (hUP₀ ui (Or.inl rfl))
    · have hdUvZk : Disjoint (triangleEdges vi wi xi) Zk := by
        apply disjoint_left.mpr
        intro e heU heZk
        rcases mem_triangleEdges.mp heZk with rfl | rfl | rfl
        · exact (mem_sdiff.mp he_k).2 (mem_sdiff.mp (hUv.2.1 heU)).1
        · rcases mem_triangleEdges.mp heU with heq | heq | heq
          · have hm : s(uk, zk) ∈ Ti := by rw [heq]; dsimp [Ti]; simp
            exact (mem_sdiff.mp hZkD.1).2 (mem_support.mpr ⟨Ti, hTiR, hm⟩)
          · exact hnotV (by simp [heq])
          · have hm : s(uk, zk) ∈ Tk := by rw [heq, hf_eq]; dsimp [Tk]; simp
            exact (mem_sdiff.mp hZkD.1).2 (mem_support.mpr ⟨Tk, hTkR, hm⟩)
        · rcases mem_triangleEdges.mp heU with heq | heq | heq
          · have hm : s(vk, zk) ∈ Ti := by rw [heq]; dsimp [Ti]; simp
            exact (mem_sdiff.mp hZkD.2.1).2 (mem_support.mpr ⟨Ti, hTiR, hm⟩)
          · exact hnotV (by simp [heq])
          · have hm : s(vk, zk) ∈ Tk := by rw [heq, hf_eq]; dsimp [Tk]; simp
            exact (mem_sdiff.mp hZkD.2.1).2 (mem_support.mpr ⟨Tk, hTkR, hm⟩)
      exact c.rest_lexMaximum.no_two_to_three (typeFamily_subset _ _ _)
        hTi hTk hneT
        (c.specialFamily_subset_typeTwo hZi) (c.specialFamily_subset_typeTwo hZk) hUv.1
        ⟨s(ui, vi), by simp⟩ ⟨s(uk, vk), by simp⟩ hUv.2.2
        hdZiZk hdUZi_v hdUvZk hZiP₀ hZkP₀ (hUP₀ vi (Or.inr rfl))

  -- Extract blue edge g₁ ∈ Zi ∩ Qk and g₂ ∈ Zi ∩ Zk
  obtain ⟨g₁, hg₁Zi, hg₁Qk⟩ := not_disjoint_iff.mp hnotDisZiQk
  obtain ⟨g₂, hg₂Zi, hg₂Zk⟩ := not_disjoint_iff.mp hnotDisZiZk
  have hg₁Blue : g₁ ∈ ({s(ui, zi), s(vi, zi)} : Finset (Sym2 V)) ∧
      g₁ ∈ ({s(uk, xk), s(vk, xk)} : Finset (Sym2 V)) := by
    rcases mem_triangleEdges.mp hg₁Zi with rfl | rfl | rfl <;>
      rcases mem_triangleEdges.mp hg₁Qk with hqk | hqk | hqk
    · exact (hneSp hqk).elim
    · exact ((mem_sdiff.mp he_i).2 (mem_sdiff.mp (mem_sdiff.mp (hqk ▸ hQkD.1)).1).1).elim
    · exact ((mem_sdiff.mp he_i).2 (mem_sdiff.mp (mem_sdiff.mp (hqk ▸ hQkD.2.1)).1).1).elim
    · exact ((mem_sdiff.mp he_k).2 (mem_sdiff.mp (mem_sdiff.mp (hqk ▸ hZiD.1)).1).1).elim
    · exact ⟨by simp, by simp [hqk]⟩
    · exact ⟨by simp, by simp [hqk]⟩
    · exact ((mem_sdiff.mp he_k).2 (mem_sdiff.mp (mem_sdiff.mp (hqk ▸ hZiD.2.1)).1).1).elim
    · exact ⟨by simp, by simp [hqk]⟩
    · exact ⟨by simp, by simp [hqk]⟩

  have hg₂Blue : g₂ ∈ ({s(ui, zi), s(vi, zi)} : Finset (Sym2 V)) ∧
      g₂ ∈ ({s(uk, zk), s(vk, zk)} : Finset (Sym2 V)) := by
    rcases mem_triangleEdges.mp hg₂Zi with rfl | rfl | rfl <;>
      rcases mem_triangleEdges.mp hg₂Zk with hzk | hzk | hzk
    · exact (hneSp hzk).elim
    · exact ((mem_sdiff.mp he_i).2 (mem_sdiff.mp (mem_sdiff.mp (hzk ▸ hZkD.1)).1).1).elim
    · exact ((mem_sdiff.mp he_i).2 (mem_sdiff.mp (mem_sdiff.mp (hzk ▸ hZkD.2.1)).1).1).elim
    · exact ((mem_sdiff.mp he_k).2 (mem_sdiff.mp (mem_sdiff.mp (hzk ▸ hZiD.1)).1).1).elim
    · exact ⟨by simp, by simp [hzk]⟩
    · exact ⟨by simp, by simp [hzk]⟩
    · exact ((mem_sdiff.mp he_k).2 (mem_sdiff.mp (mem_sdiff.mp (hzk ▸ hZiD.2.1)).1).1).elim
    · exact ⟨by simp, by simp [hzk]⟩
    · exact ⟨by simp, by simp [hzk]⟩

  -- Endpoint deduction: xk ∈ {ui, vi}
  have hndKAll : uk ≠ vk ∧ uk ≠ wk ∧ uk ≠ xk ∧ uk ≠ zk ∧ vk ≠ wk ∧ vk ≠ xk ∧ vk ≠ zk ∧
      wk ≠ xk ∧ wk ≠ zk ∧ xk ≠ zk := by simpa [List.nodup_cons, and_assoc] using hvk5
  have hzi_ne_xk : zi ≠ xk := by
    rintro rfl
    rcases mem_insert.mp hg₂Blue.1 with hg₂Eq | hg₂Eq
    · rw [hg₂Eq] at hg₂Blue
      simp only [mem_insert, mem_singleton, Sym2.eq_iff] at hg₂Blue
      rcases hg₂Blue.2 with (⟨_, h⟩ | ⟨_, h⟩) | (⟨_, h⟩ | ⟨_, h⟩) <;> simp_all
    · rw [mem_singleton.mp hg₂Eq] at hg₂Blue
      simp only [mem_insert, mem_singleton, Sym2.eq_iff] at hg₂Blue
      rcases hg₂Blue.2 with (⟨_, h⟩ | ⟨_, h⟩) | (⟨_, h⟩ | ⟨_, h⟩) <;> simp_all

  have hxk_in : xk = ui ∨ xk = vi := by
    rcases mem_insert.mp hg₁Blue.1 with hg₁Eq | hg₁Eq
    · have hm := hg₁Eq ▸ hg₁Blue.2
      simp only [mem_insert, mem_singleton, Sym2.eq_iff] at hm
      rcases hm with (⟨_, h⟩ | ⟨rfl, _⟩) | (⟨_, h⟩ | ⟨rfl, _⟩)
      · exact (hzi_ne_xk h).elim
      · exact Or.inl rfl
      · exact (hzi_ne_xk h).elim
      · exact Or.inl rfl
    · have hm := (mem_singleton.mp hg₁Eq) ▸ hg₁Blue.2
      simp only [mem_insert, mem_singleton, Sym2.eq_iff] at hm
      rcases hm with (⟨_, h⟩ | ⟨rfl, _⟩) | (⟨_, h⟩ | ⟨rfl, _⟩)
      · exact (hzi_ne_xk h).elim
      · exact Or.inr rfl
      · exact (hzi_ne_xk h).elim
      · exact Or.inr rfl

  -- Combine xk ∈ {ui, vi} with s(wi, xi) = s(uk, wk)
  rcases Sym2.eq_iff.mp hf_eq with ⟨hwi, hxi⟩ | ⟨hwi, hxi⟩
  · -- wi = uk: s(uk, xk) ∈ Ti ⊆ support c.rest, contradicting Qk ∈ c.specialFamily
    have hmTi : s(uk, xk) ∈ Ti := by
      rw [← hwi]
      rcases hxk_in with rfl | rfl <;> simp [Ti, Sym2.eq_swap]
    exact (mem_sdiff.mp hQkD.1).2 (mem_support.mpr ⟨Ti, hTiR, hmTi⟩)
  · -- xi = uk: s(uk, xk) ∈ Qi ∩ Qk, contradicting Disjoint Qi Qk
    have hmQi : s(uk, xk) ∈ Qi := by
      rw [← hxi]
      rcases hxk_in with rfl | rfl <;> dsimp [Qi] <;> simp [Sym2.eq_swap]
    have hmQk : s(uk, xk) ∈ Qk := by dsimp [Qk]; simp
    exact disjoint_left.mp (hQ.2 hQi hQk hneQ) hmQi hmQk

include hQ in
/-- Step 4 Obstruction (`k ∈ B_out`): Zero non-private opposite edges into `B_out` books. -/
theorem step4_bout_obstruction
    {ui vi wi xi zi uk vk wk xk : V}
    (hvi5 : [ui, vi, wi, xi, zi].Nodup)
    (hvk4 : [uk, vk, wk, xk].Nodup)
    (hTi : triangleEdges ui vi wi ∈ c.typeTwo)
    (hQi : triangleEdges ui vi xi ∈ Q)
    (hZi : triangleEdges ui vi zi ∈ c.specialFamily)
    (he_i : s(ui, vi) ∈ c.newEdges)
    (hTk : triangleEdges uk vk wk ∈ c.typeTwo)
    (hQk : triangleEdges uk vk xk ∈ Q)
    (he_k : s(uk, vk) ∈ c.newEdges)
    (hfkRed : s(wk, xk) ∈ c.remainingEdges \ c.old)
    (hfkOut : s(wk, xk) ∉ c.newEdges)
    (hneT : triangleEdges ui vi wi ≠ triangleEdges uk vk wk)
    (hf_eq : s(wi, xi) = s(uk, wk)) : False := by
  let Ti := triangleEdges ui vi wi
  let Qi := triangleEdges ui vi xi
  let Zi := triangleEdges ui vi zi
  let Tk := triangleEdges uk vk wk
  let Qk := triangleEdges uk vk xk
  let Ck := triangleEdges vk wk xk
  let P₀ := (c.rest.erase Ti).erase Tk
  have hTiR : Ti ∈ c.rest := c.typeTwo_subset_rest hTi
  have hTkR : Tk ∈ c.rest := c.typeTwo_subset_rest hTk
  have hneQ : Qi ≠ Qk := by
    intro heq
    have h1 : Qi ∩ c.newEdges = {s(ui, vi)} :=
      c.specialFamily_colored.red_eq_singleton (hQ.1 hQi) (by simp [Qi]) he_i
    have h2 : Qk ∩ c.newEdges = {s(uk, vk)} :=
      c.specialFamily_colored.red_eq_singleton (hQ.1 hQk) (by simp [Qk]) he_k
    have hspEq : s(ui, vi) = s(uk, vk) :=
      singleton_injective (h1.symm.trans ((congrArg (· ∩ c.newEdges) heq).trans h2))
    have hm1 : s(ui, vi) ∈ Ti := by simp [Ti]
    have hm2 : s(ui, vi) ∈ Tk := by rw [hspEq]; simp [Tk]
    exact disjoint_left.mp (c.rest_packing.2 hTiR hTkR hneT) hm1 hm2
  have hndI5 : ui ≠ vi ∧ ui ≠ wi ∧ ui ≠ xi ∧ ui ≠ zi ∧ vi ≠ wi ∧ vi ≠ xi ∧ vi ≠ zi ∧
      wi ≠ xi ∧ wi ≠ zi ∧ xi ≠ zi := by simpa [List.nodup_cons, and_assoc] using hvi5
  have hvi4 : [ui, vi, wi, xi].Nodup := by
    simp [List.nodup_cons, hndI5.1, hndI5.2.1, hndI5.2.2.1, hndI5.2.2.2.2.1,
      hndI5.2.2.2.2.2.1, hndI5.2.2.2.2.2.2.2.1]
  have hndK : uk ≠ vk ∧ uk ≠ wk ∧ uk ≠ xk ∧ vk ≠ wk ∧ vk ≠ xk ∧ wk ≠ xk := by
    simpa [List.nodup_cons, and_assoc] using hvk4

  have hZiD := special_triangle_blue_and_disjoint c hZi hTiR (by simp [Ti]) he_i
    hndI5.2.2.2.1 hndI5.2.2.2.2.2.2.1
  have hQiD := special_triangle_blue_and_disjoint c (hQ.1 hQi) hTiR (by simp [Ti]) he_i
    hndI5.2.2.1 hndI5.2.2.2.2.2.1
  have hQkD := special_triangle_blue_and_disjoint c (hQ.1 hQk) hTkR (by simp [Tk]) he_k
    hndK.2.2.1 hndK.2.2.2.2.1

  have hTkTri : Tk ∈ trianglesOn c.remainingEdges := c.rest_packing.1 hTkR
  have hukwkOld : s(uk, wk) ∈ c.oldRemaining := by
    have hneSpK : s(uk, wk) ≠ s(uk, vk) := fun h => hndK.2.2.2.1 (Sym2.congr_right.mp h).symm
    have hRem : s(uk, wk) ∈ c.remainingEdges := (mem_trianglesOn.mp hTkTri).2 (by simp [Tk])
    have hInOld : s(uk, wk) ∈ c.old := by
      by_contra hnOld
      have heq := card_le_one.mp (c.remaining_new_le_one hTkTri)
        s(uk, wk) (mem_sdiff.mpr ⟨by simp [Tk], hnOld⟩)
        s(uk, vk) (mem_sdiff.mpr ⟨by simp [Tk], (mem_sdiff.mp he_k).2⟩)
      exact hneSpK heq
    exact mem_sdiff.mpr ⟨hInOld, (mem_sdiff.mp hRem).2⟩
  have hvkwkOld : s(vk, wk) ∈ c.oldRemaining := by
    have hneSpK : s(vk, wk) ≠ s(uk, vk) := by
      intro h
      rw [Sym2.eq_swap] at h
      exact hndK.2.1 (Sym2.congr_left.mp h).symm
    have hRem : s(vk, wk) ∈ c.remainingEdges := (mem_trianglesOn.mp hTkTri).2 (by simp [Tk])
    have hInOld : s(vk, wk) ∈ c.old := by
      by_contra hnOld
      have heq := card_le_one.mp (c.remaining_new_le_one hTkTri)
        s(vk, wk) (mem_sdiff.mpr ⟨by simp [Tk], hnOld⟩)
        s(uk, vk) (mem_sdiff.mpr ⟨by simp [Tk], (mem_sdiff.mp he_k).2⟩)
      exact hneSpK heq
    exact mem_sdiff.mpr ⟨hInOld, (mem_sdiff.mp hRem).2⟩
  have hfOld : s(wi, xi) ∈ c.oldRemaining := hf_eq.symm ▸ hukwkOld

  -- Ck = triangleEdges vk wk xk ∈ typeFamily c.remainingEdges c.old 2
  have hCkType2 : Ck ∈ typeFamily c.remainingEdges c.old 2 := by
    have htriCk : IsTriangle Ck := isTriangle_triangleEdges hndK.2.2.2.1 hndK.2.2.2.2.1 hndK.2.2.2.2.2
    have hsubCk : Ck ⊆ c.remainingEdges := by
      intro e he
      rcases mem_triangleEdges.mp he with rfl | rfl | rfl
      · exact c.oldRemaining_subset_remaining hvkwkOld
      · exact c.oldRemaining_subset_remaining (mem_sdiff.mp hQkD.2.1).1
      · exact (mem_sdiff.mp hfkRed).1
    have hinterCk : Ck ∩ c.old = {s(vk, wk), s(vk, xk)} := by
      ext e
      simp only [Ck, mem_inter, mem_triangleEdges, mem_insert, mem_singleton]
      constructor
      · rintro ⟨rfl | rfl | rfl, heO⟩
        · exact Or.inl rfl
        · exact Or.inr rfl
        · exact ((mem_sdiff.mp hfkRed).2 heO).elim
      · rintro (rfl | rfl)
        · exact ⟨Or.inl rfl, (mem_sdiff.mp hvkwkOld).1⟩
        · exact ⟨Or.inr (Or.inl rfl), (mem_sdiff.mp (mem_sdiff.mp hQkD.2.1).1).1⟩
    have hpairNe : s(vk, wk) ≠ s(vk, xk) := fun h => hndK.2.2.2.2.2 (Sym2.congr_right.mp h)
    refine mem_typeFamily.mpr ⟨mem_trianglesOn.mpr ⟨htriCk, hsubCk⟩, ?_⟩
    rw [hinterCk, card_pair hpairNe]

  have hZiP₀ : Disjoint Zi (support P₀) :=
    hZiD.2.2.mono_right (support_mono (erase_subset Tk _))

  have hCkP₀ : Disjoint Ck (support P₀) := by
    apply disjoint_left.mpr
    intro e heCk heSup
    obtain ⟨X, hXP₀, heX⟩ := mem_support.mp heSup
    obtain ⟨hXneK, hX1⟩ := mem_erase.mp hXP₀
    obtain ⟨_, hXR⟩ := mem_erase.mp hX1
    rcases mem_triangleEdges.mp heCk with rfl | rfl | rfl
    · exact disjoint_left.mp (c.rest_packing.2 hTkR hXR hXneK.symm) (by simp [Tk]) heX
    · exact (mem_sdiff.mp hQkD.2.1).2 (mem_support.mpr ⟨X, hXR, heX⟩)
    · exact hfkOut (mem_sdiff.mpr ⟨mem_support.mpr ⟨X, hXR, heX⟩, (mem_sdiff.mp hfkRed).2⟩)

  have hUu := blue_candidate_in_remaining c hQ hvi4 hTiR hQi he_i hfOld (Or.inl rfl)
  have hUuP₀ : Disjoint (triangleEdges ui wi xi) (support P₀) := by
    apply disjoint_left.mpr
    intro e heU heSup
    obtain ⟨X, hXP₀, heX⟩ := mem_support.mp heSup
    obtain ⟨hXneK, hX1⟩ := mem_erase.mp hXP₀
    obtain ⟨hXneI, hXR⟩ := mem_erase.mp hX1
    rcases mem_triangleEdges.mp heU with rfl | rfl | rfl
    · exact disjoint_left.mp (c.rest_packing.2 hTiR hXR hXneI.symm) (by simp [Ti]) heX
    · exact (mem_sdiff.mp hQiD.1).2 (mem_support.mpr ⟨X, hXR, heX⟩)
    · rw [hf_eq] at heX
      exact disjoint_left.mp (c.rest_packing.2 hTkR hXR hXneK.symm) (by simp [Tk]) heX

  have hdUZi_u : Disjoint (triangleEdges ui wi xi) Zi := by
    have h5' : [ui, wi, xi, vi, zi].Nodup := by
      have h : ui ≠ vi ∧ ui ≠ wi ∧ ui ≠ xi ∧ ui ≠ zi ∧ vi ≠ wi ∧ vi ≠ xi ∧ vi ≠ zi ∧
          wi ≠ xi ∧ wi ≠ zi ∧ xi ≠ zi := by simpa [List.nodup_cons, and_assoc] using hvi5
      simp [List.nodup_cons, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1.symm,
        h.2.2.2.2.2.1.symm, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1,
        h.2.2.2.2.2.2.2.2.2]
    exact triangleEdges_disjoint_of_five_distinct h5'

  have hdUuCk : Disjoint (triangleEdges ui wi xi) Ck := by
    apply disjoint_left.mpr
    intro e heU heCk
    rcases mem_triangleEdges.mp heCk with rfl | rfl | rfl
    · rcases mem_triangleEdges.mp heU with heq | heq | heq
      · have hm1 : s(vk, wk) ∈ Ti := by rw [heq]; dsimp [Ti]; simp
        have hm2 : s(vk, wk) ∈ Tk := by dsimp [Tk]; simp
        exact disjoint_left.mp (c.rest_packing.2 hTiR hTkR hneT) hm1 hm2
      · have hm : s(ui, xi) ∈ Tk := by rw [← heq]; dsimp [Tk]; simp
        exact (mem_sdiff.mp hQiD.1).2 (mem_support.mpr ⟨Tk, hTkR, hm⟩)
      · have h1 : s(uk, wk) = s(vk, wk) := hf_eq.symm.trans heq.symm
        exact hndK.1 (Sym2.congr_left.mp h1)
    · rcases mem_triangleEdges.mp heU with heq | heq | heq
      · have hm : s(vk, xk) ∈ Ti := by rw [heq]; dsimp [Ti]; simp
        exact (mem_sdiff.mp hQkD.2.1).2 (mem_support.mpr ⟨Ti, hTiR, hm⟩)
      · have hm1 : s(vk, xk) ∈ Qi := by rw [heq]; dsimp [Qi]; simp
        have hm2 : s(vk, xk) ∈ Qk := by dsimp [Qk]; simp
        exact disjoint_left.mp (hQ.2 hQi hQk hneQ) hm1 hm2
      · have hm : s(vk, xk) ∈ Tk := by rw [heq, hf_eq]; dsimp [Tk]; simp
        exact (mem_sdiff.mp hQkD.2.1).2 (mem_support.mpr ⟨Tk, hTkR, hm⟩)
    · exact (mem_sdiff.mp hfkRed).2 (mem_sdiff.mp (hUu.2.1 heU)).1

  have hnotDisZiCk : ¬ Disjoint Zi Ck := by
    intro hdZiCk
    exact c.rest_lexMaximum.no_two_to_three (typeFamily_subset _ _ _)
      hTi hTk hneT
      (c.specialFamily_subset_typeTwo hZi) hCkType2 hUu.1
      ⟨s(ui, vi), by simp⟩ ⟨s(vk, wk), by dsimp [Ck]; simp⟩ hUu.2.2
      hdZiCk hdUZi_u hdUuCk hZiP₀ hCkP₀ hUuP₀

  obtain ⟨g, hgZi, hgCk⟩ := not_disjoint_iff.mp hnotDisZiCk
  have hgForced : ∃ αi : V, (αi = ui ∨ αi = vi) ∧ s(vk, xk) = s(αi, zi) := by
    rcases mem_triangleEdges.mp hgZi with rfl | rfl | rfl <;>
      rcases mem_triangleEdges.mp hgCk with hck | hck | hck
    · exact ((mem_sdiff.mp he_i).2 (mem_sdiff.mp (hck ▸ hvkwkOld)).1).elim
    · exact ((mem_sdiff.mp he_i).2 (mem_sdiff.mp (mem_sdiff.mp (hck ▸ hQkD.2.1)).1).1).elim
    · exact (hfkOut (hck ▸ he_i)).elim
    · exact ((mem_sdiff.mp hZiD.1).2 (mem_support.mpr ⟨Tk, hTkR, hck ▸ (by simp [Tk])⟩)).elim
    · exact ⟨ui, Or.inl rfl, hck.symm⟩
    · exact ((mem_sdiff.mp hfkRed).2 (mem_sdiff.mp (mem_sdiff.mp (hck ▸ hZiD.1)).1).1).elim
    · exact ((mem_sdiff.mp hZiD.2.1).2 (mem_support.mpr ⟨Tk, hTkR, hck ▸ (by simp [Tk])⟩)).elim
    · exact ⟨vi, Or.inr rfl, hck.symm⟩
    · exact ((mem_sdiff.mp hfkRed).2 (mem_sdiff.mp (mem_sdiff.mp (hck ▸ hZiD.2.1)).1).1).elim

  obtain ⟨αi, hαi, hvxk_eq⟩ := hgForced
  have hαiQiNotRest : s(αi, xi) ∉ support c.rest ∧ s(αi, xi) ∈ c.old ∧ s(αi, xi) ∈ Qi := by
    rcases hαi with rfl | rfl
    · exact ⟨(mem_sdiff.mp hQiD.1).2, (mem_sdiff.mp (mem_sdiff.mp hQiD.1).1).1, by simp [Qi]⟩
    · exact ⟨(mem_sdiff.mp hQiD.2.1).2, (mem_sdiff.mp (mem_sdiff.mp hQiD.2.1).1).1, by simp [Qi]⟩
  have hαiTiRest : s(αi, wi) ∈ support c.rest := by
    refine mem_support.mpr ⟨Ti, hTiR, ?_⟩
    rcases hαi with rfl | rfl <;> simp [Ti]

  -- Check all 4 endpoint orientations of s(wi, xi) = s(uk, wk) and s(vk, xk) = s(αi, zi)
  rcases Sym2.eq_iff.mp hf_eq with ⟨hwi, hxi⟩ | ⟨hwi, hxi⟩ <;>
    rcases Sym2.eq_iff.mp hvxk_eq with ⟨hvk, hxk⟩ | ⟨hvk, hxk⟩
  · -- (uk, wk) = (wi, xi), (vk, xk) = (αi, zi) => s(vk, wk) = s(αi, xi) ∈ Tk ∩ (O' \ support P')
    have hmTk : s(αi, xi) ∈ Tk := by rw [← hvk, hxi]; dsimp [Tk]; simp
    exact hαiQiNotRest.1 (mem_support.mpr ⟨Tk, hTkR, hmTk⟩)
  · -- (uk, wk) = (wi, xi), (vk, xk) = (zi, αi) => s(uk, xk) = s(wi, αi) ∈ Qk ∩ Ti
    have hmRest : s(uk, xk) ∈ support c.rest := by
      rw [← hwi, hxk, Sym2.eq_swap]; exact hαiTiRest
    exact (mem_sdiff.mp hQkD.1).2 hmRest
  · -- (uk, wk) = (xi, wi), (vk, xk) = (αi, zi) => s(uk, vk) = s(xi, αi) ∈ N ∩ c.old
    have hmOld : s(uk, vk) ∈ c.old := by
      rw [← hxi, hvk, Sym2.eq_swap]; exact hαiQiNotRest.2.1
    exact (mem_sdiff.mp he_k).2 hmOld
  · -- (uk, wk) = (xi, wi), (vk, xk) = (zi, αi) => s(uk, xk) = s(xi, αi) ∈ Qk ∩ Qi
    have hmQi : s(uk, xk) ∈ Qi := by
      rw [← hxi, hxk, Sym2.eq_swap]; exact hαiQiNotRest.2.2
    have hmQk : s(uk, xk) ∈ Qk := by dsimp [Qk]; simp
    exact disjoint_left.mp (hQ.2 hQi hQk hneQ) hmQi hmQk

/-- **Core Coverage Theorem**: `remainingCoreCover c hQ` covers every triangle of `c.remainingEdges`. -/
theorem remainingCoreCover_covers :
    IsCover (trianglesOn c.remainingEdges) (remainingCoreCover c hQ) := by
  let K := activePages c hQ
  have hK : IsPacking c.specialFamily K := activePages_packing c hQ
  intro T hT
  by_contra hnot
  have hdD : Disjoint T (remainingCoreCover c hQ) :=
    disjoint_left.mpr (fun e heT heD => hnot ⟨e, mem_inter.mpr ⟨heT, heD⟩⟩)
  have hdBase : Disjoint T (coreBase c K) := hdD.mono_right subset_union_left
  have hdOpp : Disjoint T (oppOutEdges c hQ) := hdD.mono_right subset_union_right
  have hdNew : Disjoint T c.newEdges := hdBase.mono_right (newEdges_subset_coreBase c K)

  -- T meets every page of some book p in corePages c K
  obtain ⟨p, hpMeet⟩ := Books.exists_book_all_pages_meet (coreEveryChoiceMeets c hK) hT
  have hTp : ¬ Disjoint T p.val := hpMeet p.val (Layered.mem_twoLayerPages.mpr (Or.inl rfl))
  have hpPair : p.val ∈ pairedRest c K := by
    by_contra hunp
    obtain ⟨e, heT, hep⟩ := not_disjoint_iff.mp hTp
    exact disjoint_left.mp hdBase heT
      (mem_union_left _ (mem_support.mpr ⟨p.val, mem_sdiff.mpr ⟨p.property, hunp⟩, hep⟩))
  obtain ⟨_, Qi, hQiK, hQiRed⟩ := (mem_pairedRest c).mp hpPair
  have hQiQ : Qi ∈ Q := activePages_subset_Q c hQ hQiK
  have hTQi : ¬ Disjoint T Qi :=
    hpMeet Qi (Layered.mem_twoLayerPages.mpr (Or.inr ⟨hQiK, hQiRed⟩))

  -- Extract canonical geometry of book i = (Ti, Qi)
  obtain ⟨i, ui, vi, wi, xi, hiVal, hvi4, hpEq, hqEq, hsp_i, he_i, hpages_i, hopp_i⟩ :=
    paired_book_geometry c hQ p.property hQiQ hQiRed
  have hTi_typeTwo : triangleEdges ui vi wi ∈ c.typeTwo := by
    rw [← hpEq, ← hiVal]; exact i.property
  have hQi_in_Q : triangleEdges ui vi xi ∈ Q := by
    rw [← hqEq]; exact hQiQ
  have hspNotT : s(ui, vi) ∉ T := fun hm => disjoint_left.mp hdNew hm he_i
  have hxNonempty : (T ∩ triangleEdges ui vi wi).Nonempty := by
    obtain ⟨e, heT, hep⟩ := not_disjoint_iff.mp hTp
    exact ⟨e, mem_inter.mpr ⟨heT, hpEq ▸ hep⟩⟩
  have hyNonempty : (T ∩ triangleEdges ui vi xi).Nonempty := by
    obtain ⟨e, heT, heq⟩ := not_disjoint_iff.mp hTQi
    exact ⟨e, mem_inter.mpr ⟨heT, hqEq ▸ heq⟩⟩
  have hTtri : IsTriangle T := (mem_trianglesOn.mp hT).1
  have hfiMemT : s(wi, xi) ∈ T :=
    two_page_opposite_mem hTtri hvi4 hspNotT hxNonempty hyNonempty
  have hfiRem : s(wi, xi) ∈ c.remainingEdges := (mem_trianglesOn.mp hT).2 hfiMemT
  have hfiNotD : s(wi, xi) ∉ remainingCoreCover c hQ :=
    fun hm => disjoint_left.mp hdD hfiMemT hm
  have hfiNotNew : s(wi, xi) ∉ c.newEdges :=
    fun hm => disjoint_left.mp hdNew hfiMemT hm

  -- Step 1: Qi ∉ rootPages, so Qi ∉ privPages and f_i = s(wi, xi) ∈ c.oldRemaining
  have hQiNotRoot : Qi ∉ rootPages c hQ := by
    intro hroot
    obtain ⟨_, k, hkRoot, hQi_in_k⟩ := (mem_rootPages c hQ).mp hroot
    have hik : i = k := by
      by_contra hne
      obtain ⟨e, he⟩ := c.specialFamily_colored.member_nonempty (hQ.1 hQiQ)
      have hQi_in_i : Qi ∈ (TwoLayer.book c hQ i).pages := by
        rw [hpages_i]; simp
      exact disjoint_left.mp (TwoLayer.books_disjoint c hQ hne)
        (mem_support.mpr ⟨Qi, hQi_in_i, he⟩)
        (mem_support.mpr ⟨Qi, hQi_in_k, he⟩)
    subst hik
    have hfiOpp : s(wi, xi) ∈ oppOutEdges c hQ :=
      mem_biUnion.mpr ⟨i, hkRoot, by simp [hopp_i]⟩
    exact disjoint_left.mp hdOpp hfiMemT hfiOpp

  have hQiNotPriv : triangleEdges ui vi xi ∉ privPages c Q := by
    rw [← hqEq]
    rcases (mem_activePages_iff c hQ).mp hQiK with ⟨_, hnp | hr⟩
    · exact hnp
    · exact (hQiNotRoot hr).elim

  have hfiOld : s(wi, xi) ∈ c.oldRemaining := by
    have hinOld : s(wi, xi) ∈ c.old := by
      by_contra hnOld
      exact hQiNotPriv (OppositeEdges.pair_mem_privateRed c hQ hTi_typeTwo hQi_in_Q
        he_i (mem_sdiff.mpr ⟨hfiRem, hnOld⟩) hfiNotNew)
    exact mem_sdiff.mpr ⟨hinOld, (mem_sdiff.mp hfiRem).2⟩

  have hTi_in_rest : triangleEdges ui vi wi ∈ c.rest := by
    rw [← hpEq]; exact p.property
  obtain ⟨zi, hvi5, hZiS, _⟩ := nonprivate_third_vertex c hvi4
    hTi_in_rest hQi_in_Q he_i hQiNotPriv

  -- Step 2: f_i = s(wi, xi) ∈ support c.rest (via 1-for-2 exchange), hence lies in some Tk ∈ pairedRest K
  have hfiInRest : s(wi, xi) ∈ support c.rest := by
    by_contra hnotRest
    let Ti := triangleEdges ui vi wi
    have hTiR : Ti ∈ c.rest := hTi_in_rest
    have hndI5 : ui ≠ vi ∧ ui ≠ wi ∧ ui ≠ xi ∧ ui ≠ zi ∧ vi ≠ wi ∧ vi ≠ xi ∧ vi ≠ zi ∧
        wi ≠ xi ∧ wi ≠ zi ∧ xi ≠ zi := by simpa [List.nodup_cons, and_assoc] using hvi5
    have hZiD := special_triangle_blue_and_disjoint c hZiS hTiR (by simp [Ti]) he_i
      hndI5.2.2.2.1 hndI5.2.2.2.2.2.2.1
    have hQiD := special_triangle_blue_and_disjoint c (hQ.1 hQi_in_Q) hTiR (by simp [Ti]) he_i
      hndI5.2.2.1 hndI5.2.2.2.2.2.1
    have hUu := blue_candidate_in_remaining c hQ hvi4 hTiR hQi_in_Q he_i hfiOld (Or.inl rfl)
    have hdUZi : Disjoint (triangleEdges ui wi xi) (triangleEdges ui vi zi) := by
      have h5' : [ui, wi, xi, vi, zi].Nodup := by
        simp [List.nodup_cons, hndI5.1, hndI5.2.1, hndI5.2.2.1, hndI5.2.2.2.1,
          hndI5.2.2.2.2.1.symm, hndI5.2.2.2.2.2.1.symm, hndI5.2.2.2.2.2.2.1,
          hndI5.2.2.2.2.2.2.2.1, hndI5.2.2.2.2.2.2.2.2.1, hndI5.2.2.2.2.2.2.2.2.2]
      exact triangleEdges_disjoint_of_five_distinct h5'
    have hdUuErase : Disjoint (triangleEdges ui wi xi) (support (c.rest.erase Ti)) := by
      apply disjoint_left.mpr
      intro e heU heSup
      obtain ⟨X, hXE, heX⟩ := mem_support.mp heSup
      obtain ⟨hXne, hXR⟩ := mem_erase.mp hXE
      rcases mem_triangleEdges.mp heU with rfl | rfl | rfl
      · exact disjoint_left.mp (c.rest_packing.2 hTiR hXR hXne.symm) (by simp [Ti]) heX
      · exact (mem_sdiff.mp hQiD.1).2 (mem_support.mpr ⟨X, hXR, heX⟩)
      · exact hnotRest (mem_support.mpr ⟨X, hXR, heX⟩)
    exact c.rest_lexMaximum.no_one_to_two (typeFamily_subset _ _ _)
      hTi_typeTwo (c.specialFamily_subset_typeTwo hZiS) hUu.1
      ⟨s(ui, vi), by simp⟩ hUu.2.2 hdUZi hZiD.2.2 hdUuErase

  obtain ⟨pk, hpkR, hfiPk⟩ := mem_support.mp hfiInRest
  have hpkPair : pk ∈ pairedRest c K := by
    by_contra hunp
    exact disjoint_left.mp hdBase hfiMemT
      (mem_union_left _ (mem_support.mpr ⟨pk, mem_sdiff.mpr ⟨hpkR, hunp⟩, hfiPk⟩))
  have hpkNeTi : triangleEdges ui vi wi ≠ pk := by
    rintro rfl
    have hnd : ui ≠ wi ∧ ui ≠ xi ∧ vi ≠ wi ∧ vi ≠ xi ∧ wi ≠ xi := by
      have h : ui ≠ vi ∧ ui ≠ wi ∧ ui ≠ xi ∧ vi ≠ wi ∧ vi ≠ xi ∧ wi ≠ xi := by
        simpa [List.nodup_cons, and_assoc] using hvi4
      exact ⟨h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩
    simp only [mem_triangleEdges, Sym2.eq_iff] at hfiPk
    rcases hfiPk with (⟨h1, h2⟩ | ⟨h1, h2⟩) | (⟨h1, h2⟩ | ⟨h1, h2⟩) | (⟨h1, h2⟩ | ⟨h1, h2⟩) <;>
      simp_all

  obtain ⟨_, Qk, hQkK, hQkRed⟩ := (mem_pairedRest c).mp hpkPair
  have hQkQ : Qk ∈ Q := activePages_subset_Q c hQ hQkK
  obtain ⟨k, ak, bk, wk, xk, hkVal, hvk4_raw, hpkEq, hqkEq, hsp_k, he_k, hpages_k, hopp_k⟩ :=
    paired_book_geometry c hQ hpkR hQkQ hQkRed

  -- Orient (ak, bk) as (uk, vk) so that s(wi, xi) = s(uk, wk)
  have hfiSpoke : s(wi, xi) = s(ak, wk) ∨ s(wi, xi) = s(bk, wk) := by
    rw [hpkEq] at hfiPk
    rcases mem_triangleEdges.mp hfiPk with heq | heq | heq
    · exact ((mem_sdiff.mp he_k).2 (heq ▸ (mem_sdiff.mp hfiOld).1)).elim
    · exact Or.inl heq
    · exact Or.inr heq

  have horiented : ∃ uk vk : V,
      [uk, vk, wk, xk].Nodup ∧
      pk = triangleEdges uk vk wk ∧ Qk = triangleEdges uk vk xk ∧
      s(uk, vk) ∈ c.newEdges ∧ s(wi, xi) = s(uk, wk) := by
    rcases hfiSpoke with hA | hB
    · exact ⟨ak, bk, hvk4_raw, hpkEq, hqkEq, he_k, hA⟩
    · have hswap4 : [bk, ak, wk, xk].Nodup := by
        have h : ak ≠ bk ∧ ak ≠ wk ∧ ak ≠ xk ∧ bk ≠ wk ∧ bk ≠ xk ∧ wk ≠ xk := by
          simpa [List.nodup_cons, and_assoc] using hvk4_raw
        simp [List.nodup_cons, h.1.symm, h.2.2.2.1, h.2.2.2.2.1, h.2.1, h.2.2.1, h.2.2.2.2.2]
      exact ⟨bk, ak, hswap4,
        hpkEq.trans (triangleEdges_swap_first ak bk wk).symm,
        hqkEq.trans (triangleEdges_swap_first ak bk xk).symm,
        Sym2.eq_swap ▸ he_k, hB⟩

  obtain ⟨uk, vk, hvk4, hpkUK, hqkUK, he_uk, hf_eq⟩ := horiented
  have hTk_typeTwo : triangleEdges uk vk wk ∈ c.typeTwo := by
    rw [← hpkUK, ← hkVal]; exact k.property
  have hTk_in_rest : triangleEdges uk vk wk ∈ c.rest := by
    rw [← hpkUK]; exact hpkR
  have hQk_in_Q : triangleEdges uk vk xk ∈ Q := by
    rw [← hqkUK]; exact hQkQ
  have hneTiTk : triangleEdges ui vi wi ≠ triangleEdges uk vk wk := by
    rw [← hpkUK]; exact hpkNeTi

  -- Dispatch to Step 3 (Qk ∉ privPages) or Step 4 (Qk ∈ rootPages)
  rcases (mem_activePages_iff c hQ).mp hQkK with ⟨_, hQkNP | hQkRoot⟩
  · -- Step 3: Qk ∉ privPages
    have hQkNP' : triangleEdges uk vk xk ∉ privPages c Q := by
      rw [← hqkUK]; exact hQkNP
    obtain ⟨zk, hvk5, hZkS, _⟩ := nonprivate_third_vertex c hvk4
      hTk_in_rest hQk_in_Q he_uk hQkNP'
    exact step3_nonprivate_obstruction c hQ hvi5 hvk5 hTi_typeTwo hQi_in_Q hZiS he_i
      hTk_typeTwo hQk_in_Q hZkS he_uk hneTiTk hf_eq
  · -- Step 4: Qk ∈ rootPages => k ∈ helperRoots
    obtain ⟨_, k', hk'Root, hQk_in_k'⟩ := (mem_rootPages c hQ).mp hQkRoot
    have hkk' : k = k' := by
      by_contra hne
      obtain ⟨e, he⟩ := c.specialFamily_colored.member_nonempty (hQ.1 hQkQ)
      have hQk_in_k : Qk ∈ (TwoLayer.book c hQ k).pages := by
        rw [hpages_k]; simp
      exact disjoint_left.mp (TwoLayer.books_disjoint c hQ hne)
        (mem_support.mpr ⟨Qk, hQk_in_k, he⟩)
        (mem_support.mpr ⟨Qk, hQk_in_k', he⟩)
    subst hkk'
    obtain ⟨e_opp, hop_k', he_opp_rem, he_opp_out⟩ := mem_oppositeBooks.mp hk'Root
    have hop_eq : s(wk, xk) = e_opp := Option.some.inj (hopp_k.symm.trans hop_k')
    subst hop_eq
    have hfkRed : s(wk, xk) ∈ c.remainingEdges \ c.old :=
      c.remaining_sdiff_oldRemaining ▸ he_opp_rem
    exact step4_bout_obstruction c hQ hvi5 hvk4 hTi_typeTwo hQi_in_Q hZiS he_i
      hTk_typeTwo hQk_in_Q he_uk hfkRed he_opp_out hneTiTk hf_eq

end GeometryHelpers

end OppositeElimination

namespace Construction

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {edges : Finset (Sym2 V)} (c : Construction edges)

/-- Exact partition `h_hat + h_0 = h` on `(c, r)`:
`|helperRoots| + |privZeroPages| = |privateRedPages|`. -/
theorem helperRoots_add_privZeroPages_card (r : RefinedConstruction c) :
    (HelperArborescence.helperRoots c r.second_maximum.1).card +
      (OppositeElimination.privZeroPages c r.second_maximum.1).card =
    (privateRedPages c.specialFamily c.newEdges r.second).card :=
  OppositeElimination.helperRoots_add_privZeroPages_card c r.second_maximum.1

/-- **Theorem 1.1 (`exists_opposite_elimination_cover`)**: Explicit transversal `C_core` of `G`
eliminating all non-private opposite edges (`(5'')`):
`|C_core| + 2 * c ≤ 3 * n + h_hat + 2 * h_0`. -/
theorem exists_opposite_elimination_cover (r : RefinedConstruction c) :
    ∃ C, IsCover (trianglesOn edges) C ∧
      C.card + 2 * r.second.card ≤
        3 * c.initial.card +
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
  refine ⟨support c.first ∪ D, cover_union_residual hres, ?_⟩
  have hsize := c.first_packing.card_support_uniform
    (fun _ hT => trianglesOn_card (c.first_packing.1 hT))
  have hu := card_union_le (support c.first) D
  have hp := c.first_rest_card_le
  omega

/-- **Theorem 1.1 (`opposite_elimination_cover`)**: Inequality `(5'')` on `(c, r)`:
`τ(G) + 2 * c ≤ 3 * n + h_hat + 2 * h_0`. -/
theorem opposite_elimination_cover (r : RefinedConstruction c) :
    transversalNumber (trianglesOn edges) + 2 * r.second.card ≤
      3 * c.initial.card +
        (HelperArborescence.helperRoots c r.second_maximum.1).card +
        2 * (OppositeElimination.privZeroPages c r.second_maximum.1).card := by
  obtain ⟨C, hC, hc⟩ := c.exists_opposite_elimination_cover r
  have ht := hC.number_le
  omega

end Construction

end TuzaBound
