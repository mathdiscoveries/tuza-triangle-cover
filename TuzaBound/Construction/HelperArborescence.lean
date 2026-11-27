/-
Copyright (c) 2026 Tyler B. Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Helper-Arborescence Coupling Lemma (Lemma 1.1) for `TuzaBound`.
-/
module

public import TuzaBound.Construction.RandomCover
public import TuzaBound.Construction.BookCover
public import TuzaBound.Probability.Arborescence

/-!
# Lemma 1.1: Helper-Arborescence Coupling (`+3/8 h` → `+1/4 h`)

Improves Sichen Wang's random-bipartition cover bound from `+ (3/8) h` to `+ (1/4) h`:

```
4 * transversalNumber (trianglesOn edges) + 4 * Q.card ≤
  6 * c.initial.card + 10 * c.first.card + 6 * c.typeTwo.card +
    (privateRedPages c.specialFamily c.newEdges Q).card
```

## Proof Structure (`m1-report.md` §2.2)

1. **Helper functional digraph (`helperNext`)**: On `I := {T // T ∈ c.typeTwo}`, place a directed
   arc `j → i` (`helperNext c hQ j = some i`) iff `(book c hQ j).opposite = some (book c hQ i).spine`.
   Injectivity of book spines (`spine_injective`) gives out-degree `≤ 1`, and every sink
   `r₀ ∈ oppositeBooks` (`B_out`, `x_i y_i ∉ N`) has out-degree `0` (`helperNext_eq_none_of_roots`).
2. **All-depth `2^r` binary-toggle exchange (`basin_third_vertex_child`)**: Along any directed
   chain `idx : Fin (k + 1) → I` from `idx 0 = r₀ ∈ B_out` to `idx (Fin.last k) = v`, every book
   `books (idx s)` is a two-page `.double` book providing a disjoint blue-spoke candidate pair
   `Book.cand (books (idx s)) false` and `Book.cand (books (idx s)) true` in `F_2`. By
   `exists_disjoint_spokes`, any uncovered-candidate triangle `Z = u_v v_v z ∈ F_2` avoiding `W`
   with `z ∉ {u_v, v_v, x_v, y_v}` avoids at least one candidate at every depth `0 ≤ s ≤ k`.
   Maximality of `B* = c.typeTwo` in `F_2` then forces `Z` to meet both pages of some external
   two-page book `j ∉ image idx`, whence `two_page_triangle` yields `j → v` and `z ∈ spine(j)`.
3. **Spine-expectation saving (`helper_arborescence_random_cover`)**: Step 2 bounds
   `|S_v| ≤ 2 + 2 * indeg(v)` for every `v ∈ basin r₀`, giving
   `Pr[e_v ∈ D_red] ≤ 1/2 - (1/8) * 4^(-indeg v)`. Combining with `Arborescence.global_prob_sum_le`
   (`(1/8)*4^(-k) ≥ 1/8 - (3/32)*k` and `∑ indeg = |T_i| - 1`) saves `(1/8) |B_out|` on `D_red ∩ N`,
   reducing `(3/8) |B_out|` to `(1/4) |B_out| ≤ (1/4) h`.
-/

@[expose] public section

namespace TuzaBound

open Finset
open scoped BigOperators

namespace Book

/-- Candidate `F_2` triangles `(x, y, u)` (`ε = false`) and `(x, y, v)` (`ε = true`)
associated to a two-page book `.double u v x y hv`. -/
def cand {V : Type*} [DecidableEq V] (b : Book V) (ε : Bool) : Finset (Sym2 V) :=
  match b with
  | .double u v x y _ => if ε then triangleEdges x y v else triangleEdges x y u
  | _ => ∅

theorem exists_double_of_opposite {V : Type*} {b : Book V} {e : Sym2 V}
    (hop : b.opposite = some e) :
    ∃ u v x y : V, ∃ hv : [u, v, x, y].Nodup,
      b = Book.double u v x y hv ∧ b.spine = s(u, v) ∧ e = s(x, y) := by
  cases b with
  | single u v x hv => simp [Book.opposite] at hop
  | triple u v x y z hv => simp [Book.opposite] at hop
  | double u v x y hv =>
    exact ⟨u, v, x, y, hv, rfl, rfl, (Option.some.inj hop).symm⟩

end Book

namespace HelperArborescence

section Geometry

variable {V : Type*} [DecidableEq V]

/-- The two spoke sets `{s(u_s, x_s), s(u_s, y_s)}` and `{s(v_s, x_s), s(v_s, y_s)}`
of a 4-vertex two-page book are disjoint. -/
theorem spokes_disjoint {us vs xs ys : V} (hv : [us, vs, xs, ys].Nodup) :
    Disjoint ({s(us, xs), s(us, ys)} : Finset (Sym2 V))
      ({s(vs, xs), s(vs, ys)} : Finset (Sym2 V)) := by
  have hnd : us ≠ vs ∧ us ≠ xs ∧ us ≠ ys ∧ vs ≠ xs ∧ vs ≠ ys ∧ xs ≠ ys := by
    simpa [List.nodup_cons, and_assoc] using hv
  apply disjoint_left.mpr
  intro e he0 he1
  simp only [mem_insert, mem_singleton] at he0 he1
  rcases he0 with rfl | rfl <;> rcases he1 with h | h <;>
    simp only [Sym2.eq_iff] at h <;> rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp_all

/-- If `s(a, z) ∈ {s(us, xs), s(us, ys)}` and `s(b, z) ∈ {s(vs, xs), s(vs, ys)}`
with `[us, vs, xs, ys].Nodup`, then `s(a, b) = s(us, vs)` and `z ∈ {xs, ys}`. -/
theorem pair_spokes_forced {us vs xs ys a b z : V} (hv : [us, vs, xs, ys].Nodup)
    (h0 : s(a, z) ∈ ({s(us, xs), s(us, ys)} : Finset (Sym2 V)))
    (h1 : s(b, z) ∈ ({s(vs, xs), s(vs, ys)} : Finset (Sym2 V))) :
    s(a, b) = s(us, vs) ∧ (z = xs ∨ z = ys) := by
  have hnd : us ≠ vs ∧ us ≠ xs ∧ us ≠ ys ∧ vs ≠ xs ∧ vs ≠ ys ∧ xs ≠ ys := by
    simpa [List.nodup_cons, and_assoc] using hv
  simp only [mem_insert, mem_singleton, Sym2.eq_iff] at h0 h1
  rcases h0 with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
    rcases h1 with (⟨h1a, h1b⟩ | ⟨h1a, h1b⟩) | (⟨h1a, h1b⟩ | ⟨h1a, h1b⟩) <;>
    simp_all

/-- Unless `s(uk, vk) = s(us, vs)` and `z ∈ {xs, ys}`, the spoke pair `{s(uk, z), s(vk, z)}`
is disjoint from at least one of `{s(us, xs), s(us, ys)}` or `{s(vs, xs), s(vs, ys)}`. -/
theorem exists_disjoint_spokes {us vs xs ys uk vk z : V}
    (hv : [us, vs, xs, ys].Nodup)
    (hnot : ¬ (s(uk, vk) = s(us, vs) ∧ (z = xs ∨ z = ys))) :
    Disjoint ({s(uk, z), s(vk, z)} : Finset (Sym2 V)) {s(us, xs), s(us, ys)} ∨
    Disjoint ({s(uk, z), s(vk, z)} : Finset (Sym2 V)) {s(vs, xs), s(vs, ys)} := by
  by_contra hboth
  push Not at hboth
  obtain ⟨h0, h1⟩ := hboth
  obtain ⟨e0, he0W, he0S⟩ := not_disjoint_iff.mp h0
  obtain ⟨e1, he1W, he1S⟩ := not_disjoint_iff.mp h1
  have hne01 : e0 ≠ e1 := fun heq =>
    disjoint_left.mp (spokes_disjoint hv) he0S (heq ▸ he1S)
  simp only [mem_insert, mem_singleton] at he0W he1W
  rcases he0W with rfl | rfl <;> rcases he1W with rfl | rfl
  · exact hne01 rfl
  · exact hnot (pair_spokes_forced hv he0S he1S)
  · obtain ⟨hsp, hz⟩ := pair_spokes_forced hv he0S he1S
    exact hnot ⟨Sym2.eq_swap.trans hsp, hz⟩
  · exact hne01 rfl

end Geometry

section Coupling

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {edges : Finset (Sym2 V)} (c : Construction edges)
variable {Q : Finset (Finset (Sym2 V))} (hQ : IsPacking c.specialFamily Q)

/-- Finite vertex set of an unoriented edge `e : Sym2 V` (at most 2 vertices). -/
def edgeVerts (e : Sym2 V) : Finset V :=
  univ.filter (fun w => w ∈ e)

@[simp] theorem mem_edgeVerts {e : Sym2 V} {w : V} :
    w ∈ edgeVerts e ↔ w ∈ e := by
  simp [edgeVerts]

theorem card_edgeVerts_le_two (e : Sym2 V) : (edgeVerts e).card ≤ 2 := by
  refine Sym2.inductionOn e (fun a b => ?_)
  have heq : edgeVerts s(a, b) = ({a, b} : Finset V) := by
    ext w
    simp [edgeVerts]
  rw [heq]
  exact card_le_two

/-- Distinct members of `c.typeTwo` have distinct spines in `TwoLayer.book`. -/
theorem spine_injective :
    Function.Injective (fun i : {T // T ∈ c.typeTwo} => (TwoLayer.book c hQ i).spine) := by
  intro i₁ i₂ heq
  dsimp at heq
  by_contra hne
  have hm₁ : (TwoLayer.book c hQ i₁).spine ∈ i₁.val :=
    Book.spine_mem_page _ (TwoLayer.book_parent_mem c hQ i₁)
  have hm₂ : (TwoLayer.book c hQ i₂).spine ∈ i₂.val :=
    Book.spine_mem_page _ (TwoLayer.book_parent_mem c hQ i₂)
  exact disjoint_left.mp (TwoLayer.books_disjoint c hQ hne)
    (mem_support.mpr ⟨i₁.val, TwoLayer.book_parent_mem c hQ i₁, hm₁⟩)
    (mem_support.mpr ⟨i₂.val, TwoLayer.book_parent_mem c hQ i₂, heq ▸ hm₂⟩)

/-- Every edge of `c.newEdges` is the spine of some book in `TwoLayer.book c hQ`. -/
theorem exists_book_with_spine {e : Sym2 V} (he : e ∈ c.newEdges) :
    ∃ i : {T // T ∈ c.typeTwo}, (TwoLayer.book c hQ i).spine = e := by
  have heR : e ∈ redEdges (c.remainingEdges \ c.old) c.typeTwo := by
    rwa [← c.newEdges_eq_red_typeTwo]
  obtain ⟨heSup, _⟩ := mem_redEdges.mp heR
  obtain ⟨p, hp, hep⟩ := mem_support.mp heSup
  let i : {T // T ∈ c.typeTwo} := ⟨p, hp⟩
  refine ⟨i, ?_⟩
  have hcard : (i.val ∩ c.newEdges).card ≤ 1 := by
    rw [Construction.typeTwo_red_card i]
  have hs : (TwoLayer.book c hQ i).spine ∈ i.val ∩ c.newEdges := by
    rw [TwoLayer.book_spine]
    exact Construction.typeTwoSpine_mem i
  exact card_le_one.mp hcard _ hs e (mem_inter.mpr ⟨hep, he⟩)

/-- Helper partial function on `{T // T ∈ c.typeTwo}`: `j → i` iff
`(book j).opposite = some (book i).spine`. -/
noncomputable def helperNext (j : {T // T ∈ c.typeTwo}) : Option {T // T ∈ c.typeTwo} := by
  classical
  exact
    if h : ∃ i : {T // T ∈ c.typeTwo},
        (TwoLayer.book c hQ j).opposite = some (TwoLayer.book c hQ i).spine
    then some (Classical.choose h)
    else none

theorem helperNext_eq_some_iff {j i : {T // T ∈ c.typeTwo}} :
    helperNext c hQ j = some i ↔
      (TwoLayer.book c hQ j).opposite = some (TwoLayer.book c hQ i).spine := by
  classical
  unfold helperNext
  constructor
  · intro h
    split_ifs at h with hex
    · simp only [Option.some.injEq] at h
      exact h ▸ Classical.choose_spec hex
  · intro hop
    have hex : ∃ k : {T // T ∈ c.typeTwo},
        (TwoLayer.book c hQ j).opposite = some (TwoLayer.book c hQ k).spine := ⟨i, hop⟩
    simp only [hex, ↓reduceDIte, Option.some.injEq]
    exact spine_injective c hQ (Option.some.inj ((Classical.choose_spec hex).symm.trans hop))

/-- Sinks `B_out`: books whose opposite edge lies in `c.remainingEdges \ c.oldRemaining`
outside `c.newEdges`. -/
noncomputable def helperRoots : Finset {T // T ∈ c.typeTwo} :=
  oppositeBooks c.remainingEdges c.oldRemaining c.newEdges (TwoLayer.book c hQ)

theorem helperNext_eq_none_of_roots {r : {T // T ∈ c.typeTwo}}
    (hr : r ∈ helperRoots c hQ) : helperNext c hQ r = none := by
  by_contra hne
  obtain ⟨i, hi⟩ := Option.ne_none_iff_exists'.mp hne
  have hop := (helperNext_eq_some_iff c hQ).mp hi
  obtain ⟨e, hrop, _, heN⟩ := mem_oppositeBooks.mp hr
  have heq : e = (TwoLayer.book c hQ i).spine := Option.some.inj (hrop.symm.trans hop)
  exact heN (heq ▸ TwoLayer.book_spine_mem c hQ i)

/-- Every book `i` whose opposite edge `e_opp` lies in `c.remainingEdges \ c.old` has
both `Book.cand (book i) ε` in `typeFamily c.remainingEdges c.old 2`, with old edges
contained in `support (book i).pages` and unique non-old edge `e_opp`. -/
theorem cand_properties {i : {T // T ∈ c.typeTwo}} {e_opp : Sym2 V}
    (hop : (TwoLayer.book c hQ i).opposite = some e_opp)
    (heopp : e_opp ∈ c.remainingEdges \ c.old) (ε : Bool) :
    (TwoLayer.book c hQ i).cand ε ∈ typeFamily c.remainingEdges c.old 2 ∧
    ((TwoLayer.book c hQ i).cand ε).Nonempty ∧
    (TwoLayer.book c hQ i).cand ε \ {e_opp} ⊆
      support (TwoLayer.book c hQ i).pages ∩ c.old := by
  obtain ⟨u, v, x, y, hv, hb, hsp, hexy⟩ := Book.exists_double_of_opposite hop
  have hnd : u ≠ v ∧ u ≠ x ∧ u ≠ y ∧ v ≠ x ∧ v ≠ y ∧ x ≠ y := by
    simpa [List.nodup_cons, and_assoc] using hv
  rcases hnd with ⟨huv, hux, huy, hvx, hvy, hxy⟩
  have hpx : triangleEdges u v x ∈ (TwoLayer.book c hQ i).pages := by simp [hb, Book.pages]
  have hpy : triangleEdges u v y ∈ (TwoLayer.book c hQ i).pages := by simp [hb, Book.pages]
  have huxO : s(u, x) ∈ c.oldRemaining :=
    TwoLayer.book_blue_old c hQ i hpx (by simp [hsp, hvx.symm, huv])
  have hvxO : s(v, x) ∈ c.oldRemaining :=
    TwoLayer.book_blue_old c hQ i hpx (by simp [hsp, hux.symm, huv.symm])
  have huyO : s(u, y) ∈ c.oldRemaining :=
    TwoLayer.book_blue_old c hQ i hpy (by simp [hsp, hvy.symm, huv])
  have hvyO : s(v, y) ∈ c.oldRemaining :=
    TwoLayer.book_blue_old c hQ i hpy (by simp [hsp, huy.symm, huv.symm])
  have huxSup : s(u, x) ∈ support (TwoLayer.book c hQ i).pages :=
    mem_support.mpr ⟨triangleEdges u v x, hpx, by simp⟩
  have hvxSup : s(v, x) ∈ support (TwoLayer.book c hQ i).pages :=
    mem_support.mpr ⟨triangleEdges u v x, hpx, by simp⟩
  have huySup : s(u, y) ∈ support (TwoLayer.book c hQ i).pages :=
    mem_support.mpr ⟨triangleEdges u v y, hpy, by simp⟩
  have hvySup : s(v, y) ∈ support (TwoLayer.book c hQ i).pages :=
    mem_support.mpr ⟨triangleEdges u v y, hpy, by simp⟩
  obtain ⟨heoppRem, heoppNotOld⟩ := mem_sdiff.mp heopp
  subst e_opp
  cases ε
  · -- ε = false: triangleEdges x y u
    have hcand : (TwoLayer.book c hQ i).cand false = triangleEdges x y u := by
      simp [hb, Book.cand]
    rw [hcand]
    have htri : IsTriangle (triangleEdges x y u) :=
      isTriangle_triangleEdges hxy hux.symm huy.symm
    have hsubRem : triangleEdges x y u ⊆ c.remainingEdges := by
      intro e he
      rcases mem_triangleEdges.mp he with rfl | rfl | rfl
      · exact heoppRem
      · exact c.oldRemaining_subset_remaining (Sym2.eq_swap ▸ huxO)
      · exact c.oldRemaining_subset_remaining (Sym2.eq_swap ▸ huyO)
    have hinter : triangleEdges x y u ∩ c.old = {s(x, u), s(y, u)} := by
      ext e
      simp only [mem_inter, mem_triangleEdges, mem_insert, mem_singleton]
      constructor
      · rintro ⟨rfl | rfl | rfl, heOld⟩
        · exact (heoppNotOld heOld).elim
        · exact Or.inl rfl
        · exact Or.inr rfl
      · rintro (rfl | rfl)
        · exact ⟨Or.inr (Or.inl rfl), (mem_sdiff.mp (Sym2.eq_swap ▸ huxO)).1⟩
        · exact ⟨Or.inr (Or.inr rfl), (mem_sdiff.mp (Sym2.eq_swap ▸ huyO)).1⟩
    have hpairNe : s(x, u) ≠ s(y, u) := fun h => hxy (Sym2.congr_left.mp h)
    refine ⟨mem_typeFamily.mpr ⟨mem_trianglesOn.mpr ⟨htri, hsubRem⟩, ?_⟩,
      ⟨s(x, y), by simp⟩, ?_⟩
    · rw [hinter, card_pair hpairNe]
    · intro e he
      obtain ⟨heT, heNe⟩ := mem_sdiff.mp he
      rcases mem_triangleEdges.mp heT with rfl | rfl | rfl
      · exact (heNe (mem_singleton_self _)).elim
      · exact mem_inter.mpr ⟨Sym2.eq_swap ▸ huxSup, (mem_sdiff.mp (Sym2.eq_swap ▸ huxO)).1⟩
      · exact mem_inter.mpr ⟨Sym2.eq_swap ▸ huySup, (mem_sdiff.mp (Sym2.eq_swap ▸ huyO)).1⟩
  · -- ε = true: triangleEdges x y v
    have hcand : (TwoLayer.book c hQ i).cand true = triangleEdges x y v := by
      simp [hb, Book.cand]
    rw [hcand]
    have htri : IsTriangle (triangleEdges x y v) :=
      isTriangle_triangleEdges hxy hvx.symm hvy.symm
    have hsubRem : triangleEdges x y v ⊆ c.remainingEdges := by
      intro e he
      rcases mem_triangleEdges.mp he with rfl | rfl | rfl
      · exact heoppRem
      · exact c.oldRemaining_subset_remaining (Sym2.eq_swap ▸ hvxO)
      · exact c.oldRemaining_subset_remaining (Sym2.eq_swap ▸ hvyO)
    have hinter : triangleEdges x y v ∩ c.old = {s(x, v), s(y, v)} := by
      ext e
      simp only [mem_inter, mem_triangleEdges, mem_insert, mem_singleton]
      constructor
      · rintro ⟨rfl | rfl | rfl, heOld⟩
        · exact (heoppNotOld heOld).elim
        · exact Or.inl rfl
        · exact Or.inr rfl
      · rintro (rfl | rfl)
        · exact ⟨Or.inr (Or.inl rfl), (mem_sdiff.mp (Sym2.eq_swap ▸ hvxO)).1⟩
        · exact ⟨Or.inr (Or.inr rfl), (mem_sdiff.mp (Sym2.eq_swap ▸ hvyO)).1⟩
    have hpairNe : s(x, v) ≠ s(y, v) := fun h => hxy (Sym2.congr_left.mp h)
    refine ⟨mem_typeFamily.mpr ⟨mem_trianglesOn.mpr ⟨htri, hsubRem⟩, ?_⟩,
      ⟨s(x, y), by simp⟩, ?_⟩
    · rw [hinter, card_pair hpairNe]
    · intro e he
      obtain ⟨heT, heNe⟩ := mem_sdiff.mp he
      rcases mem_triangleEdges.mp heT with rfl | rfl | rfl
      · exact (heNe (mem_singleton_self _)).elim
      · exact mem_inter.mpr ⟨Sym2.eq_swap ▸ hvxSup, (mem_sdiff.mp (Sym2.eq_swap ▸ hvxO)).1⟩
      · exact mem_inter.mpr ⟨Sym2.eq_swap ▸ hvySup, (mem_sdiff.mp (Sym2.eq_swap ▸ hvyO)).1⟩

/-- Every edge in `support (book j).pages` outside `c.old` equals `(book j).spine`. -/
theorem support_book_not_old_eq_spine {j : {T // T ∈ c.typeTwo}} {e : Sym2 V}
    (heSup : e ∈ support (TwoLayer.book c hQ j).pages) (heNotOld : e ∉ c.old) :
    e = (TwoLayer.book c hQ j).spine := by
  obtain ⟨U, hU, heU⟩ := mem_support.mp heSup
  by_contra hne
  have heRem := TwoLayer.book_blue_old c hQ j hU (mem_sdiff.mpr ⟨heU, mem_singleton.not.mpr hne⟩)
  exact heNotOld (mem_sdiff.mp heRem).1

/-- For a triangle `Z = triangleEdges uv_u uv_v z ∈ F_2` with red edge `s(uv_u, uv_v) ∈ N`,
both spokes `s(uv_u, z)` and `s(uv_v, z)` lie in `c.oldRemaining`. -/
theorem third_vertex_spokes_oldRemaining {u v z : V}
    (huv : u ≠ v) (huz : u ≠ z) (hvz : v ≠ z)
    (hspine : s(u, v) ∈ c.newEdges)
    (hZ : triangleEdges u v z ∈ typeFamily c.remainingEdges c.old 2) :
    s(u, z) ∈ c.oldRemaining ∧ s(v, z) ∈ c.oldRemaining := by
  obtain ⟨hZtri, hZoldCard⟩ := mem_typeFamily.mp hZ
  have hZsub := (mem_trianglesOn.mp hZtri).2
  have huvNotOld : s(u, v) ∉ c.old := (mem_sdiff.mp hspine).2
  have htcard : (triangleEdges u v z).card = 3 := triangleEdges_card huv huz hvz
  have hpart := card_sdiff_add_card_inter (triangleEdges u v z) c.old
  have hsdiffCard : (triangleEdges u v z \ c.old).card ≤ 1 := by omega
  have huvSdiff : s(u, v) ∈ triangleEdges u v z \ c.old :=
    mem_sdiff.mpr ⟨by simp, huvNotOld⟩
  have huzOld : s(u, z) ∈ c.old := by
    by_contra hn
    have heq := card_le_one.mp hsdiffCard _ (mem_sdiff.mpr ⟨by simp, hn⟩) _ huvSdiff
    exact hvz (Sym2.congr_right.mp heq).symm
  have hvzOld : s(v, z) ∈ c.old := by
    by_contra hn
    have heq := card_le_one.mp hsdiffCard _ (mem_sdiff.mpr ⟨by simp, hn⟩) _ huvSdiff
    exact huz (Sym2.congr_left.mp (Sym2.eq_swap.trans heq)).symm
  exact ⟨mem_sdiff.mpr ⟨huzOld, (mem_sdiff.mp (hZsub (by simp))).2⟩,
    mem_sdiff.mpr ⟨hvzOld, (mem_sdiff.mp (hZsub (by simp))).2⟩⟩

/-- **Step 2 (`basin_third_vertex_child`)**: All-depth `2^r` binary-toggle exchange invariant.
If `v` lies in the ancestor basin of `r₀ ∈ helperRoots` with `books v = .double u_v v_v x_v y_v hv_v`,
then every `z ∉ {u_v, v_v, x_v, y_v}` forming an `F_2` triangle `u_v v_v z` whose blue spokes
avoid `fixedOld` belongs to the spine of some child `j ∈ childrenOf (helperNext c hQ) v`. -/
theorem basin_third_vertex_child {r₀ v : {T // T ∈ c.typeTwo}}
    (hr₀ : r₀ ∈ helperRoots c hQ)
    (hvBasin : v ∈ Arborescence.basin (helperNext c hQ) r₀)
    {uv vv xv yv z : V} {hvv : [uv, vv, xv, yv].Nodup}
    (hbv : TwoLayer.book c hQ v = Book.double uv vv xv yv hvv)
    (huz : uv ≠ z) (hvz : vv ≠ z) (hxz : z ≠ xv) (hyz : z ≠ yv)
    (hZ : triangleEdges uv vv z ∈ typeFamily c.remainingEdges c.old 2)
    (huzW : s(uv, z) ∉ TwoLayer.fixedOld c Q)
    (hvzW : s(vv, z) ∉ TwoLayer.fixedOld c Q) :
    ∃ j ∈ Arborescence.childrenOf (helperNext c hQ) v,
      z ∈ (TwoLayer.book c hQ j).spine := by
  classical
  let books := TwoLayer.book c hQ
  let F₂ := typeFamily c.remainingEdges c.old 2
  have hsp_v : (books v).spine = s(uv, vv) := by simp [books, hbv, Book.spine]
  have huv : uv ≠ vv := fun h => (List.nodup_cons.mp hvv).1 (by simp [h])
  have hspineN : s(uv, vv) ∈ c.newEdges := hsp_v ▸ TwoLayer.book_spine_mem c hQ v
  obtain ⟨huzOldRem, hvzOldRem⟩ :=
    third_vertex_spokes_oldRemaining c huv huz hvz hspineN hZ
  have huzOld : s(uv, z) ∈ c.old := (mem_sdiff.mp huzOldRem).1
  have hvzOld : s(vv, z) ∈ c.old := (mem_sdiff.mp hvzOldRem).1
  have huvNotOld : s(uv, vv) ∉ c.old := (mem_sdiff.mp hspineN).2

  obtain ⟨k, hk⟩ := Arborescence.mem_basin.mp hvBasin
  obtain ⟨idx, hidx0, hidxLast, hidxInj, _, hidxStep⟩ :=
    Arborescence.exists_chain_from_sink hk (helperNext_eq_none_of_roots c hQ hr₀)

  obtain ⟨e₀, he₀op, he₀rem, he₀notN⟩ := mem_oppositeBooks.mp hr₀
  have he₀R : e₀ ∈ c.remainingEdges \ c.old := c.remaining_sdiff_oldRemaining ▸ he₀rem

  let oppEdge : Fin (k + 1) → Sym2 V := fun s =>
    if hs : s.val = 0 then e₀
    else (books (idx ⟨s.val - 1, by omega⟩)).spine

  have hopp_spec (s : Fin (k + 1)) :
      (books (idx s)).opposite = some (oppEdge s) ∧
      oppEdge s ∈ c.remainingEdges \ c.old ∧
      (s.val = 0 → oppEdge s ∉ c.newEdges) ∧
      (∀ t : Fin k, s = t.succ → oppEdge s = (books (idx t.castSucc)).spine) := by
    refine Fin.cases ?_ ?_ s
    · refine ⟨?_, ?_, ?_, ?_⟩
      · simpa [oppEdge, hidx0] using he₀op
      · simpa [oppEdge] using he₀R
      · intro _; simpa [oppEdge] using he₀notN
      · intro t ht; exact (Fin.succ_ne_zero t ht.symm).elim
    · intro t
      have hval : (t.succ).val ≠ 0 := Nat.succ_ne_zero t.val
      have hop := (helperNext_eq_some_iff c hQ).mp (hidxStep t)
      have hspT : (books (idx t.castSucc)).spine ∈ c.remainingEdges \ c.old := by
        have hN := TwoLayer.book_spine_mem c hQ (idx t.castSucc)
        exact mem_sdiff.mpr ⟨c.newEdges_subset_remaining hN, (mem_sdiff.mp hN).2⟩
      have heqOpp : oppEdge t.succ = (books (idx t.castSucc)).spine := by
        simp [oppEdge]
        rfl
      refine ⟨heqOpp ▸ hop, heqOpp ▸ hspT, fun h0 => (hval h0).elim, ?_⟩
      intro t' ht'
      cases Fin.succ_inj.mp ht'
      exact heqOpp

  have hopp_inj : Function.Injective oppEdge := by
    intro s₁ s₂
    refine Fin.cases ?_ ?_ s₁ <;> refine Fin.cases ?_ ?_ s₂
    · intro _; rfl
    · intro t₂ heq
      have h0 := (hopp_spec 0).2.2.1 rfl
      have h1 : oppEdge t₂.succ ∈ c.newEdges := by
        rw [(hopp_spec t₂.succ).2.2.2 t₂ rfl]
        exact TwoLayer.book_spine_mem c hQ _
      exact (h0 (heq ▸ h1)).elim
    · intro t₁ heq
      have h0 := (hopp_spec 0).2.2.1 rfl
      have h1 : oppEdge t₁.succ ∈ c.newEdges := by
        rw [(hopp_spec t₁.succ).2.2.2 t₁ rfl]
        exact TwoLayer.book_spine_mem c hQ _
      exact (h0 (heq.symm ▸ h1)).elim
    · intro t₁ t₂ heq
      rw [(hopp_spec t₁.succ).2.2.2 t₁ rfl, (hopp_spec t₂.succ).2.2.2 t₂ rfl] at heq
      have hcastEq := hidxInj (spine_injective c hQ heq)
      exact congrArg Fin.succ (Fin.ext (by simpa using congrArg Fin.val hcastEq))

  have hopp_ne_v (s : Fin (k + 1)) : oppEdge s ≠ s(uv, vv) := by
    refine Fin.cases ?_ ?_ s
    · intro heq
      exact (hopp_spec 0).2.2.1 rfl (heq ▸ hspineN)
    · intro t heq
      rw [(hopp_spec t.succ).2.2.2 t rfl, ← hsp_v, ← hidxLast] at heq
      have hcastEq := hidxInj (spine_injective c hQ heq)
      have hval := congrArg Fin.val hcastEq
      simp only [Fin.val_castSucc, Fin.val_last] at hval
      exact Nat.ne_of_lt t.isLt hval

  -- Choose ε_s : Bool at each depth s so that Z is disjoint from (books (idx s)).cand ε_s
  have hex_eps (s : Fin (k + 1)) :
      ∃ ε : Bool, Disjoint (triangleEdges uv vv z) ((books (idx s)).cand ε) := by
    obtain ⟨hopS, heS, _, _⟩ := hopp_spec s
    obtain ⟨us, vs, xs, ys, hvs, hbs, hsps, hexys⟩ := Book.exists_double_of_opposite hopS
    have hnot : ¬ (s(uv, vv) = s(us, vs) ∧ (z = xs ∨ z = ys)) := by
      rintro ⟨hspEq, hzxy⟩
      have hv_eq_s : idx (Fin.last k) = idx s := by
        apply spine_injective c hQ
        change (books (idx (Fin.last k))).spine = (books (idx s)).spine
        rw [hidxLast, hsp_v, hsps, hspEq]
      have hsLast : s = Fin.last k := (hidxInj hv_eq_s).symm
      subst hsLast
      rw [hidxLast] at hbs
      have hdEq : Book.double uv vv xv yv hvv = Book.double us vs xs ys hvs :=
        hbv.symm.trans hbs
      injection hdEq with _ _ hxx hyy
      rcases hzxy with rfl | rfl
      · exact hxz hxx.symm
      · exact hyz hyy.symm
    have hspokes := exists_disjoint_spokes hvs hnot
    have hoppNotOld : s(xs, ys) ∉ c.old := hexys ▸ (mem_sdiff.mp heS).2
    have hneOpp : s(uv, vv) ≠ s(xs, ys) := fun h => hopp_ne_v s (hexys.trans h.symm)
    rcases hspokes with hd0 | hd1
    · refine ⟨false, ?_⟩
      simp only [hbs, Book.cand, Bool.false_eq_true, ↓reduceIte]
      apply disjoint_left.mpr
      intro e heZ heC
      have heC' : e = s(xs, ys) ∨ e ∈ ({s(us, xs), s(us, ys)} : Finset (Sym2 V)) := by
        rcases mem_triangleEdges.mp heC with rfl | rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (by simp [Sym2.eq_swap])
        · exact Or.inr (by simp [Sym2.eq_swap])
      rcases mem_triangleEdges.mp heZ with rfl | rfl | rfl
      · rcases heC' with heq | heSp
        · exact hneOpp heq
        · have heOld := (cand_properties c hQ hopS heS false).2.2
          have : s(uv, vv) ∈ (books (idx s)).cand false \ {oppEdge s} := by
            simp only [hbs, Book.cand, Bool.false_eq_true, ↓reduceIte, hexys,
              mem_sdiff, mem_triangleEdges, mem_singleton]
            refine ⟨?_, hneOpp⟩
            simp only [mem_insert, mem_singleton] at heSp
            rcases heSp with h | h <;> simp [h, Sym2.eq_swap]
          exact huvNotOld (mem_inter.mp (heOld this)).2
      · rcases heC' with heq | heSp
        · exact hoppNotOld (heq ▸ huzOld)
        · exact disjoint_left.mp hd0 (by simp) heSp
      · rcases heC' with heq | heSp
        · exact hoppNotOld (heq ▸ hvzOld)
        · exact disjoint_left.mp hd0 (by simp) heSp
    · refine ⟨true, ?_⟩
      simp only [hbs, Book.cand, ↓reduceIte]
      apply disjoint_left.mpr
      intro e heZ heC
      have heC' : e = s(xs, ys) ∨ e ∈ ({s(vs, xs), s(vs, ys)} : Finset (Sym2 V)) := by
        rcases mem_triangleEdges.mp heC with rfl | rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (by simp [Sym2.eq_swap])
        · exact Or.inr (by simp [Sym2.eq_swap])
      rcases mem_triangleEdges.mp heZ with rfl | rfl | rfl
      · rcases heC' with heq | heSp
        · exact hneOpp heq
        · have heOld := (cand_properties c hQ hopS heS true).2.2
          have : s(uv, vv) ∈ (books (idx s)).cand true \ {oppEdge s} := by
            simp only [hbs, Book.cand, ↓reduceIte, hexys,
              mem_sdiff, mem_triangleEdges, mem_singleton]
            refine ⟨?_, hneOpp⟩
            simp only [mem_insert, mem_singleton] at heSp
            rcases heSp with h | h <;> simp [h, Sym2.eq_swap]
          exact huvNotOld (mem_inter.mp (heOld this)).2
      · rcases heC' with heq | heSp
        · exact hoppNotOld (heq ▸ huzOld)
        · exact disjoint_left.mp hd1 (by simp) heSp
      · rcases heC' with heq | heSp
        · exact hoppNotOld (heq ▸ hvzOld)
        · exact disjoint_left.mp hd1 (by simp) heSp

  choose eps heps using hex_eps
  let candF : Fin (k + 1) → Finset (Sym2 V) := fun s => (books (idx s)).cand (eps s)

  have hcand_F2 (s : Fin (k + 1)) : candF s ∈ F₂ :=
    (cand_properties c hQ (hopp_spec s).1 (hopp_spec s).2.1 (eps s)).1
  have hcand_ne (s : Fin (k + 1)) : (candF s).Nonempty :=
    (cand_properties c hQ (hopp_spec s).1 (hopp_spec s).2.1 (eps s)).2.1

  have hcand_disj : Pairwise (fun s₁ s₂ => Disjoint (candF s₁) (candF s₂)) := by
    intro s₁ s₂ hne
    apply disjoint_left.mpr
    intro e he₁ he₂
    have hc₁ := (cand_properties c hQ (hopp_spec s₁).1 (hopp_spec s₁).2.1 (eps s₁)).2.2
    have hc₂ := (cand_properties c hQ (hopp_spec s₂).1 (hopp_spec s₂).2.1 (eps s₂)).2.2
    by_cases heOpp₁ : e = oppEdge s₁
    · subst heOpp₁
      have hnotOld₁ : oppEdge s₁ ∉ c.old := (mem_sdiff.mp (hopp_spec s₁).2.1).2
      have heOpp₂ : oppEdge s₁ = oppEdge s₂ := by
        by_contra hne2
        exact hnotOld₁ (mem_inter.mp (hc₂ (mem_sdiff.mpr ⟨he₂, mem_singleton.not.mpr hne2⟩))).2
      exact hne (hopp_inj heOpp₂)
    · have hSup₁ := hc₁ (mem_sdiff.mpr ⟨he₁, mem_singleton.not.mpr heOpp₁⟩)
      by_cases heOpp₂ : e = oppEdge s₂
      · subst heOpp₂
        exact (mem_sdiff.mp (hopp_spec s₂).2.1).2 (mem_inter.mp hSup₁).2
      · have hSup₂ := hc₂ (mem_sdiff.mpr ⟨he₂, mem_singleton.not.mpr heOpp₂⟩)
        exact disjoint_left.mp (TwoLayer.books_disjoint c hQ (fun h => hne (hidxInj h)))
          (mem_inter.mp hSup₁).1 (mem_inter.mp hSup₂).1

  let chainIdx : Finset {T // T ∈ c.typeTwo} := univ.image idx
  let extIdx : Finset {T // T ∈ c.typeTwo} := univ \ chainIdx

  have hcand_ext_disj (s : Fin (k + 1)) {j : {T // T ∈ c.typeTwo}} (hj : j ∈ extIdx) :
      Disjoint (candF s) (support (books j).pages) := by
    have hjNot : j ∉ chainIdx := (mem_sdiff.mp hj).2
    have hjNeIdx : idx s ≠ j := fun h => hjNot (mem_image.mpr ⟨s, mem_univ _, h⟩)
    have hcS := (cand_properties c hQ (hopp_spec s).1 (hopp_spec s).2.1 (eps s)).2.2
    apply disjoint_left.mpr
    intro e heC heSupJ
    by_cases heOpp : e = oppEdge s
    · subst heOpp
      have hnotOld : oppEdge s ∉ c.old := (mem_sdiff.mp (hopp_spec s).2.1).2
      have hspJ := support_book_not_old_eq_spine c hQ heSupJ hnotOld
      revert hspJ
      refine Fin.cases ?_ ?_ s
      · intro hspJ0
        exact (hopp_spec 0).2.2.1 rfl (hspJ0 ▸ TwoLayer.book_spine_mem c hQ j)
      · intro t hspJt
        rw [(hopp_spec t.succ).2.2.2 t rfl] at hspJt
        have hjEq := spine_injective c hQ hspJt.symm
        exact hjNot (mem_image.mpr ⟨t.castSucc, mem_univ _, hjEq.symm⟩)
    · have hSupS := (mem_inter.mp (hcS (mem_sdiff.mpr ⟨heC, mem_singleton.not.mpr heOpp⟩))).1
      exact disjoint_left.mp (TwoLayer.books_disjoint c hQ hjNeIdx) hSupS heSupJ

  -- Maximality of c.typeTwo in F₂ forces Z to meet all pages of some external book j ∈ extIdx
  have hex_j : ∃ j ∈ extIdx, ∀ U ∈ (books j).pages, ¬ Disjoint (triangleEdges uv vv z) U := by
    by_contra hnone
    push Not at hnone
    choose f hf_mem hf_disj using fun j : {x // x ∈ extIdx} => hnone j.val j.property
    let P_chain : Finset (Finset (Sym2 V)) := univ.image candF
    let P_ext : Finset (Finset (Sym2 V)) := univ.image f
    have hcandInj : Function.Injective candF := by
      intro s₁ s₂ heq
      by_contra hne
      obtain ⟨e, he⟩ := hcand_ne s₁
      exact disjoint_left.mp (hcand_disj hne) he (heq ▸ he)
    have hf_F2 (j : {x // x ∈ extIdx}) : f j ∈ F₂ := by
      have hm := hf_mem j
      rw [TwoLayer.book_pages] at hm
      exact TwoLayer.pages_subset c hQ j.val hm
    have hf_ne (j : {x // x ∈ extIdx}) : (f j).Nonempty :=
      trianglesOn_nonempty (typeFamily_subset _ _ _ (hf_F2 j))
    have hf_pair_disj : Pairwise (fun j₁ j₂ : {x // x ∈ extIdx} => Disjoint (f j₁) (f j₂)) := by
      intro j₁ j₂ hne
      have hvne : j₁.val ≠ j₂.val := fun h => hne (Subtype.ext h)
      exact (TwoLayer.books_disjoint c hQ hvne).mono
        (Books.page_subset_support (hf_mem j₁)) (Books.page_subset_support (hf_mem j₂))
    have hfInj : Function.Injective f := by
      intro j₁ j₂ heq
      by_contra hne
      obtain ⟨e, he⟩ := hf_ne j₁
      exact disjoint_left.mp (hf_pair_disj hne) he (heq ▸ he)
    have hpack_chain : IsPacking F₂ P_chain := by
      refine ⟨?_, ?_⟩
      · intro T hT
        obtain ⟨s, _, rfl⟩ := mem_image.mp hT
        exact hcand_F2 s
      · intro T hT U hU hne
        obtain ⟨s₁, _, rfl⟩ := mem_image.mp hT
        obtain ⟨s₂, _, rfl⟩ := mem_image.mp hU
        exact hcand_disj (fun h => hne (congrArg candF h))
    have hpack_ext : IsPacking F₂ P_ext := by
      refine ⟨?_, ?_⟩
      · intro T hT
        obtain ⟨j, _, rfl⟩ := mem_image.mp hT
        exact hf_F2 j
      · intro T hT U hU hne
        obtain ⟨j₁, _, rfl⟩ := mem_image.mp hT
        obtain ⟨j₂, _, rfl⟩ := mem_image.mp hU
        exact hf_pair_disj (fun h => hne (congrArg f h))
    have hd_chain_ext : Disjoint (support P_chain) (support P_ext) := by
      apply disjoint_left.mpr
      intro e he1 he2
      obtain ⟨T1, hT1, heT1⟩ := mem_support.mp he1
      obtain ⟨s, _, rfl⟩ := mem_image.mp hT1
      obtain ⟨T2, hT2, heT2⟩ := mem_support.mp he2
      obtain ⟨j, _, rfl⟩ := mem_image.mp hT2
      exact disjoint_left.mp (hcand_ext_disj s j.property) heT1
        (mem_support.mpr ⟨f j, hf_mem j, heT2⟩)
    have hpack_union : IsPacking F₂ (P_chain ∪ P_ext) :=
      hpack_chain.union hpack_ext hd_chain_ext
    have hd_Z : Disjoint (triangleEdges uv vv z) (support (P_chain ∪ P_ext)) := by
      apply disjoint_left.mpr
      intro e heZ heSup
      obtain ⟨T, hT, heT⟩ := mem_support.mp heSup
      rcases mem_union.mp hT with hTc | hTe
      · obtain ⟨s, _, rfl⟩ := mem_image.mp hTc
        exact disjoint_left.mp (heps s) heZ heT
      · obtain ⟨j, _, rfl⟩ := mem_image.mp hTe
        exact disjoint_left.mp (hf_disj j) heZ heT
    have hpack_all : IsPacking F₂ (insert (triangleEdges uv vv z) (P_chain ∪ P_ext)) :=
      packing_insert hpack_union hZ hd_Z
    have hZ_notMem : triangleEdges uv vv z ∉ P_chain ∪ P_ext := by
      intro hm
      exact disjoint_left.mp hd_Z (by simp : s(uv, vv) ∈ triangleEdges uv vv z)
        (mem_support.mpr ⟨_, hm, by simp⟩)
    have hdisj_sets : Disjoint P_chain P_ext :=
      disjoint_of_support_disjoint
        (fun T hT => by obtain ⟨s, _, rfl⟩ := mem_image.mp hT; exact hcand_ne s)
        hd_chain_ext
    have hcard_chain : P_chain.card = k + 1 := by
      rw [card_image_of_injective _ hcandInj, card_univ, Fintype.card_fin]
    have hcard_chainIdx : chainIdx.card = k + 1 := by
      rw [card_image_of_injective _ hidxInj, card_univ, Fintype.card_fin]
    have hcard_ext : P_ext.card = extIdx.card := by
      rw [card_image_of_injective _ hfInj, card_univ, Fintype.card_coe]
    have hcard_split : extIdx.card + chainIdx.card = c.typeTwo.card := by
      have hs := card_sdiff_add_card_eq_card (subset_univ chainIdx)
      simpa [extIdx, Fintype.card_coe] using hs
    have hcard_all : (insert (triangleEdges uv vv z) (P_chain ∪ P_ext)).card =
        c.typeTwo.card + 1 := by
      rw [card_insert_of_notMem hZ_notMem, card_union_of_disjoint hdisj_sets,
        hcard_chain, hcard_ext]
      omega
    have hle := c.typeTwo_maximum.2 _ hpack_all
    omega

  obtain ⟨j, hjExt, hjMeet⟩ := hex_j
  have hjNotChain : j ∉ chainIdx := (mem_sdiff.mp hjExt).2
  have hjNeV : j ≠ v := fun h =>
    hjNotChain (mem_image.mpr ⟨Fin.last k, mem_univ _, hidxLast.trans h.symm⟩)
  have hsp_ne : (books j).spine ≠ s(uv, vv) := by
    rw [← hsp_v]
    exact fun h => hjNeV (spine_injective c hQ h)
  have hsp_j_notMem : (books j).spine ∉ triangleEdges uv vv z := by
    intro hm
    have hspN := TwoLayer.book_spine_mem c hQ j
    have hspNotOld : (books j).spine ∉ c.old := (mem_sdiff.mp hspN).2
    rcases mem_triangleEdges.mp hm with h | h | h
    · exact hsp_ne h
    · exact hspNotOld (h ▸ huzOld)
    · exact hspNotOld (h ▸ hvzOld)

  have hZtri : IsTriangle (triangleEdges uv vv z) :=
    isTriangle_triangleEdges huv huz hvz

  generalize hbj : books j = bj at hjMeet hsp_j_notMem
  cases bj with
  | single uj vj xj hvj =>
    exfalso
    have hc1 : (books j).pages.card = 1 := by simp [books, hbj, Book.pages]
    have hUmem : triangleEdges uj vj xj ∈ (books j).pages := by simp [books, hbj, Book.pages]
    obtain ⟨e, heZ, heU⟩ :=
      not_disjoint_iff.mp (hjMeet (triangleEdges uj vj xj) (by simp [Book.pages]))
    have heNotSp : e ≠ (TwoLayer.book c hQ j).spine := by
      intro h
      have h' : e = (Book.single uj vj xj hvj).spine := by
        simpa [books, hbj] using h
      exact hsp_j_notMem (h' ▸ heZ)
    have heOldRem := TwoLayer.book_blue_old c hQ j hUmem
      (mem_sdiff.mpr ⟨heU, mem_singleton.not.mpr heNotSp⟩)
    have heW := TwoLayer.book_single_fixedOld c hQ j hc1 _ hUmem
      (mem_inter.mpr ⟨heU, heOldRem⟩)
    rcases mem_triangleEdges.mp heZ with rfl | rfl | rfl
    · exact huvNotOld (mem_sdiff.mp heOldRem).1
    · exact huzW heW
    · exact hvzW heW
  | triple uj vj xj yj zj hvj =>
    have hc3 : (books j).pages.card = 3 := by
      have hp := (books j).pages_card
      simpa [books, hbj, Book.pageCount] using hp
    have hle2 : (books j).pages.card ≤ 2 := by
      rw [TwoLayer.book_pages]
      exact TwoLayer.pages_card_le_two c hQ j
    omega
  | double uj vj xj yj hvj =>
    have hndJ : uj ≠ vj ∧ uj ≠ xj ∧ uj ≠ yj ∧ vj ≠ xj ∧ vj ≠ yj ∧ xj ≠ yj := by
      simpa [List.nodup_cons, and_assoc] using hvj
    rcases hndJ with ⟨huvJ, huxJ, huyJ, hvxJ, hvyJ, hxyJ⟩
    have hspJ : (TwoLayer.book c hQ j).spine = s(uj, vj) := by
      simpa [books, Book.spine] using congrArg Book.spine hbj
    have hpxJ : triangleEdges uj vj xj ∈ (TwoLayer.book c hQ j).pages := by
      simp [books, hbj, Book.pages]
    have hpyJ : triangleEdges uj vj yj ∈ (TwoLayer.book c hQ j).pages := by
      simp [books, hbj, Book.pages]
    have huxJO : s(uj, xj) ∈ c.old :=
      (mem_sdiff.mp (TwoLayer.book_blue_old c hQ j hpxJ (by simp [hspJ, hvxJ.symm, huvJ]))).1
    have hvxJO : s(vj, xj) ∈ c.old :=
      (mem_sdiff.mp (TwoLayer.book_blue_old c hQ j hpxJ (by simp [hspJ, huxJ.symm, huvJ.symm]))).1
    have huyJO : s(uj, yj) ∈ c.old :=
      (mem_sdiff.mp (TwoLayer.book_blue_old c hQ j hpyJ (by simp [hspJ, hvyJ.symm, huvJ]))).1
    have hvyJO : s(vj, yj) ∈ c.old :=
      (mem_sdiff.mp (TwoLayer.book_blue_old c hQ j hpyJ (by simp [hspJ, huyJ.symm, huvJ.symm]))).1

    have hmX : (triangleEdges uv vv z ∩ triangleEdges uj vj xj).Nonempty := by
      obtain ⟨e, h1, h2⟩ :=
        not_disjoint_iff.mp (hjMeet (triangleEdges uj vj xj) (by simp [Book.pages]))
      exact ⟨e, mem_inter.mpr ⟨h1, h2⟩⟩
    have hmY : (triangleEdges uv vv z ∩ triangleEdges uj vj yj).Nonempty := by
      obtain ⟨e, h1, h2⟩ :=
        not_disjoint_iff.mp (hjMeet (triangleEdges uj vj yj) (by simp [Book.pages]))
      exact ⟨e, mem_inter.mpr ⟨h1, h2⟩⟩
    have hnotSpJ : s(uj, vj) ∉ triangleEdges uv vv z := by
      simpa [Book.spine] using hsp_j_notMem

    have hshape := two_page_triangle hZtri hvj hnotSpJ hmX hmY
    have huv_eq_xy : s(uv, vv) = s(xj, yj) := by
      have huvMem : s(uv, vv) ∈ triangleEdges uv vv z := by simp
      rcases hshape with hEq | hEq <;> rw [hEq] at huvMem <;>
        rcases mem_triangleEdges.mp huvMem with h | h | h
      · exact (huvNotOld (h ▸ huxJO)).elim
      · exact (huvNotOld (h ▸ huyJO)).elim
      · exact h
      · exact (huvNotOld (h ▸ hvxJO)).elim
      · exact (huvNotOld (h ▸ hvyJO)).elim
      · exact h

    have hop_jv : (books j).opposite = some (books v).spine := by
      simp [books, hbj, Book.opposite, hsp_v, huv_eq_xy]
    have hjChild : j ∈ Arborescence.childrenOf (helperNext c hQ) v :=
      Arborescence.mem_childrenOf.mpr ((helperNext_eq_some_iff c hQ).mpr hop_jv)

    have hzNotXY : z ∉ s(xj, yj) := by
      rw [← huv_eq_xy, Sym2.mem_iff]
      rintro (rfl | rfl)
      · exact huz rfl
      · exact hvz rfl

    have hzSpine : z ∈ (books j).spine := by
      rw [hspJ, Sym2.mem_iff]
      have huzMem : s(uv, z) ∈ triangleEdges uv vv z := by simp
      rcases hshape with hEq | hEq <;> rw [hEq] at huzMem <;>
        rcases mem_triangleEdges.mp huzMem with h | h | h
      · have hzMem : z ∈ s(uj, xj) := h ▸ Sym2.mem_mk_right uv z
        rcases Sym2.mem_iff.mp hzMem with rfl | rfl
        · exact Or.inl rfl
        · exact (hzNotXY (by simp)).elim
      · have hzMem : z ∈ s(uj, yj) := h ▸ Sym2.mem_mk_right uv z
        rcases Sym2.mem_iff.mp hzMem with rfl | rfl
        · exact Or.inl rfl
        · exact (hzNotXY (by simp)).elim
      · exact (hzNotXY (h ▸ Sym2.mem_mk_right uv z)).elim
      · have hzMem : z ∈ s(vj, xj) := h ▸ Sym2.mem_mk_right uv z
        rcases Sym2.mem_iff.mp hzMem with rfl | rfl
        · exact Or.inr rfl
        · exact (hzNotXY (by simp)).elim
      · have hzMem : z ∈ s(vj, yj) := h ▸ Sym2.mem_mk_right uv z
        rcases Sym2.mem_iff.mp hzMem with rfl | rfl
        · exact Or.inr rfl
        · exact (hzNotXY (by simp)).elim
      · exact (hzNotXY (h ▸ Sym2.mem_mk_right uv z)).elim

    exact ⟨j, hjChild, hzSpine⟩

/-- Every node `v ∈ basin r₀` (`r₀ ∈ helperRoots`) has spine addition probability at most
`1/2 - (1/8) * (1/4)^(|childrenOf v|)`. -/
theorem spine_prob_le_in_basin {r₀ v : {T // T ∈ c.typeTwo}}
    (hr₀ : r₀ ∈ helperRoots c hQ)
    (hvBasin : v ∈ Arborescence.basin (helperNext c hQ) r₀) :
    bitAverage (fun χ : V → Bool =>
      if (TwoLayer.book c hQ v).spine ∈
        cutAddedEdges c.remainingEdges (TwoLayer.fixedOld c Q) c.oldRemaining χ
      then (1 : ℚ) else 0) ≤
    1 / 2 - (1 / 8 : ℚ) *
      (1 / 4 : ℚ) ^ (Arborescence.childrenOf (helperNext c hQ) v).card := by
  classical
  obtain ⟨k, hk⟩ := Arborescence.mem_basin.mp hvBasin
  have hexOpp : ∃ e, (TwoLayer.book c hQ v).opposite = some e := by
    cases k with
    | zero =>
      simp only [Arborescence.reachIn, Option.some.injEq] at hk
      subst hk
      obtain ⟨e, hop, _, _⟩ := mem_oppositeBooks.mp hr₀
      exact ⟨e, hop⟩
    | succ m =>
      cases hnv : helperNext c hQ v with
      | none => simp [Arborescence.reachIn, hnv] at hk
      | some u =>
        exact ⟨_, (helperNext_eq_some_iff c hQ).mp hnv⟩
  obtain ⟨e_opp, hop_v⟩ := hexOpp
  obtain ⟨uv, vv, xv, yv, hvv, hbv, hsp_v, _⟩ := Book.exists_double_of_opposite hop_v
  have huv : uv ≠ vv := fun h => (List.nodup_cons.mp hvv).1 (by simp [h])

  let Sv : Finset V := univ.filter (fun z =>
    uv ≠ z ∧ vv ≠ z ∧
    triangleEdges uv vv z ∈ typeFamily c.remainingEdges c.old 2 ∧
    s(uv, z) ∉ TwoLayer.fixedOld c Q ∧
    s(vv, z) ∉ TwoLayer.fixedOld c Q)

  have huSv : uv ∉ Sv := by simp [Sv]
  have hvSv : vv ∉ Sv := by simp [Sv]

  -- Bound |Sv| ≤ 2 + 2 * indeg(v)
  let children := Arborescence.childrenOf (helperNext c hQ) v
  have hSv_sub :
      Sv ⊆ ({xv, yv} : Finset V) ∪
        children.biUnion (fun j => edgeVerts (TwoLayer.book c hQ j).spine) := by
    intro z hz
    obtain ⟨_, ⟨huz, hvz, hZ, huzW, hvzW⟩⟩ := mem_filter.mp hz
    by_cases hxy : z ∈ ({xv, yv} : Finset V)
    · exact mem_union_left _ hxy
    · simp only [mem_insert, mem_singleton, not_or] at hxy
      obtain ⟨j, hjC, hzSp⟩ := basin_third_vertex_child c hQ hr₀ hvBasin hbv
        huz hvz hxy.1 hxy.2 hZ huzW hvzW
      exact mem_union_right _ (mem_biUnion.mpr ⟨j, hjC, mem_edgeVerts.mpr hzSp⟩)

  have hSv_card : Sv.card ≤ 2 + 2 * children.card := by
    have hc1 := card_le_card hSv_sub
    have hc2 := card_union_le ({xv, yv} : Finset V)
      (children.biUnion (fun j => edgeVerts (TwoLayer.book c hQ j).spine))
    have hcxy : ({xv, yv} : Finset V).card ≤ 2 := card_le_two
    have hcbi : (children.biUnion (fun j => edgeVerts (TwoLayer.book c hQ j).spine)).card ≤
        2 * children.card := by
      calc
        (children.biUnion (fun j => edgeVerts (TwoLayer.book c hQ j).spine)).card ≤
            ∑ j ∈ children, (edgeVerts (TwoLayer.book c hQ j).spine).card := card_biUnion_le
        _ ≤ ∑ _j ∈ children, 2 := sum_le_sum (fun j _ => card_edgeVerts_le_two _)
        _ = 2 * children.card := by simp [Nat.mul_comm]
    omega

  -- Pointwise implication: spine ∈ cutAddedEdges → spineEvent uv vv Sv χ
  have hpoint (χ : V → Bool) :
      (if (TwoLayer.book c hQ v).spine ∈
        cutAddedEdges c.remainingEdges (TwoLayer.fixedOld c Q) c.oldRemaining χ
      then (1 : ℚ) else 0) ≤
      (if spineEvent uv vv Sv χ then (1 : ℚ) else 0) := by
    by_cases hAdd : (TwoLayer.book c hQ v).spine ∈
        cutAddedEdges c.remainingEdges (TwoLayer.fixedOld c Q) c.oldRemaining χ
    · have hNC := cutAddedEdges_noncrossing
        (fun _ hT => c.remaining_oldRemaining_ge_two hT) χ hAdd
      rw [hsp_v] at hAdd hNC
      have hsame : χ uv = χ vv := (noncrossingEdge_pair χ uv vv).mp hNC
      obtain ⟨Z, hZres, heZnew⟩ := mem_cutAddedEdges.mp hAdd
      obtain ⟨hZtriOn, hZdisj⟩ := mem_residual.mp hZres
      have hZtype : Z ∈ typeFamily c.remainingEdges c.old 2 := by
        rw [← c.typeFamily_oldRemaining 2]
        exact new_edge_forces_typeTwo hZtriOn (c.remaining_oldRemaining_ge_two hZtriOn) heZnew
      obtain ⟨z, huz, hvz, rfl⟩ :=
        (mem_trianglesOn.mp hZtriOn).1.exists_third_of_mem (mem_sdiff.mp heZnew).1
      have huzW : s(uv, z) ∉ TwoLayer.fixedOld c Q := fun hw =>
        disjoint_left.mp hZdisj (by simp) (mem_union_left _ hw)
      have hvzW : s(vv, z) ∉ TwoLayer.fixedOld c Q := fun hw =>
        disjoint_left.mp hZdisj (by simp) (mem_union_left _ hw)
      have hzSv : z ∈ Sv := mem_filter.mpr ⟨mem_univ z, huz, hvz, hZtype, huzW, hvzW⟩
      have hspineN : s(uv, vv) ∈ c.newEdges := hsp_v ▸ TwoLayer.book_spine_mem c hQ v
      obtain ⟨huzOldRem, _⟩ := third_vertex_spokes_oldRemaining c huv huz hvz hspineN hZtype
      have hzDiff : χ z ≠ χ uv := by
        intro heq
        have hnc_uz : noncrossingEdge χ s(uv, z) :=
          (noncrossingEdge_pair χ uv z).mpr heq.symm
        exact disjoint_left.mp hZdisj (by simp : s(uv, z) ∈ triangleEdges uv vv z)
          (mem_union_right _ (mem_filter.mpr ⟨huzOldRem, hnc_uz⟩))
      have hspEv : spineEvent uv vv Sv χ := ⟨hsame, z, hzSv, hzDiff⟩
      rw [hsp_v]
      simp [hAdd, hspEv]
    · simp [hAdd]; split_ifs <;> norm_num

  have havg_le : bitAverage (fun χ : V → Bool =>
      if (TwoLayer.book c hQ v).spine ∈
        cutAddedEdges c.remainingEdges (TwoLayer.fixedOld c Q) c.oldRemaining χ
      then (1 : ℚ) else 0) ≤
      bitAverage (fun χ : V → Bool => if spineEvent uv vv Sv χ then (1 : ℚ) else 0) :=
    finiteAverage_mono _ _ hpoint
  rw [spineEvent_average uv vv Sv huv huSv hvSv] at havg_le
  have hpow_le : (1 / 8 : ℚ) * (1 / 4 : ℚ) ^ children.card ≤
      (1 / 2 : ℚ) ^ (Sv.card + 1) := by
    have hexp : Sv.card + 1 ≤ 2 * children.card + 3 := by omega
    have hp := pow_le_pow_of_le_one (a := (1 / 2 : ℚ)) (by norm_num) (by norm_num) hexp
    have heq : (1 / 2 : ℚ) ^ (2 * children.card + 3) =
        (1 / 8 : ℚ) * (1 / 4 : ℚ) ^ children.card := by
      rw [pow_add, pow_mul]
      ring
    linarith
  linarith

include hQ in
/-- Unrelaxed helper-arborescence random-cover estimate (`+1/4 h_hat`) in the remaining graph `G'`,
prior to relaxing `|B_out| ≤ h`. -/
theorem remaining_helper_random_cover_unrelaxed :
    4 * transversalNumber (trianglesOn c.remainingEdges) + 4 * Q.card ≤
      2 * c.oldRemaining.card + 6 * c.typeTwo.card +
        (helperRoots c hQ).card := by
  classical
  let A' := c.remainingEdges
  let O' := c.oldRemaining
  let N := c.newEdges
  let W := TwoLayer.fixedOld c Q
  let books := TwoLayer.book c hQ
  let roots := helperRoots c hQ

  have hNO : Disjoint N O' := c.newEdges_disjoint_old.mono_right sdiff_subset
  have hW : W ⊆ O' := TwoLayer.fixedOld_subset c
  have hOdiag : ∀ e ∈ O', ¬ e.IsDiag := fun _ he => c.old_not_diag (mem_sdiff.mp he).1
  have hchoice : Books.EveryChoiceMeets (typeFamily A' O' 2) (fun p => (books p).pages) := by
    rw [c.typeFamily_oldRemaining]
    exact TwoLayer.books_everyChoiceMeets c hQ

  let prob : {T // T ∈ c.typeTwo} → ℚ := fun i =>
    bitAverage (fun χ : V → Bool =>
      if (books i).spine ∈ cutAddedEdges A' W O' χ then (1 : ℚ) else 0)

  have hprob_half (i : {T // T ∈ c.typeTwo}) : prob i ≤ 1 / 2 := by
    have hpt (χ : V → Bool) :
        (if (books i).spine ∈ cutAddedEdges A' W O' χ then (1 : ℚ) else 0) ≤
        (if noncrossingEdge χ (books i).spine then (1 : ℚ) else 0) := by
      by_cases hAdd : (books i).spine ∈ cutAddedEdges A' W O' χ
      · have hNC := cutAddedEdges_noncrossing
          (fun _ hT => c.remaining_oldRemaining_ge_two hT) χ hAdd
        simp [hAdd, hNC]
      · simp [hAdd]; split_ifs <;> norm_num
    calc
      prob i ≤ bitAverage (fun χ => if noncrossingEdge χ (books i).spine then (1 : ℚ) else 0) :=
        finiteAverage_mono _ _ hpt
      _ = 1 / 2 := noncrossingEdge_average _ (c.newEdges_not_diag (TwoLayer.book_spine_mem c hQ i))

  have hprob_sum : ∑ i : {T // T ∈ c.typeTwo}, prob i ≤
      (1 / 2 : ℚ) * c.typeTwo.card - (1 / 8 : ℚ) * roots.card := by
    simpa only [Fintype.card_coe] using
      Arborescence.global_prob_sum_le
        (fun r hr => helperNext_eq_none_of_roots c hQ hr)
        prob hprob_half
        (fun r hr v hv => spine_prob_le_in_basin c hQ hr hv)

  have hinN (χ : V → Bool) :
      (cutAddedEdges A' W O' χ ∩ N).card ≤
        (univ.filter (fun i : {T // T ∈ c.typeTwo} =>
          (books i).spine ∈ cutAddedEdges A' W O' χ)).card := by
    let K := univ.filter (fun i : {T // T ∈ c.typeTwo} =>
      (books i).spine ∈ cutAddedEdges A' W O' χ)
    have hsub : cutAddedEdges A' W O' χ ∩ N ⊆ K.image (fun i => (books i).spine) := by
      intro e he
      obtain ⟨heAdd, heN⟩ := mem_inter.mp he
      obtain ⟨i, rfl⟩ := exists_book_with_spine c hQ heN
      exact mem_image.mpr ⟨i, mem_filter.mpr ⟨mem_univ i, heAdd⟩, rfl⟩
    exact (card_le_card hsub).trans card_image_le

  have houtN (χ : V → Bool) :
      (cutAddedEdges A' W O' χ \ N).card ≤
        (roots.filter (fun i => (books i).cutEvent χ)).card :=
    card_le_book_events books roots _ χ (fun _ he =>
      cutAddedEdges_book_witness books
        (fun _ hT => c.remaining_oldRemaining_ge_two hT) hNO
        (TwoLayer.book_spine_mem c hQ)
        (fun p _ hU => TwoLayer.book_blue_old c hQ p hU)
        (TwoLayer.book_single_fixedOld c hQ) hchoice χ he)

  have hpoint (χ : V → Bool) :
      ((cutCover A' W O' χ).card : ℚ) ≤
        ((selectedOld W O' χ).card : ℚ) +
        ((univ.filter (fun i : {T // T ∈ c.typeTwo} =>
          (books i).spine ∈ cutAddedEdges A' W O' χ)).card : ℚ) +
        ((roots.filter (fun i => (books i).cutEvent χ)).card : ℚ) := by
    have hsp := cutCover_card_split_le A' W O' N χ
    have h1 := hinN χ
    have h2 := houtN χ
    exact_mod_cast (show (cutCover A' W O' χ).card ≤
      (selectedOld W O' χ).card +
      (univ.filter (fun i : {T // T ∈ c.typeTwo} =>
        (books i).spine ∈ cutAddedEdges A' W O' χ)).card +
      (roots.filter (fun i => (books i).cutEvent χ)).card by omega)

  have havg := finiteAverage_mono _ _ hpoint
  rw [finiteAverage_add, finiteAverage_add] at havg
  change bitAverage _ ≤ bitAverage _ + bitAverage _ + bitAverage _ at havg
  rw [selectedOld_average hW hOdiag] at havg

  have havg_inN :
      bitAverage (fun χ : V → Bool =>
        ((univ.filter (fun i : {T // T ∈ c.typeTwo} =>
          (books i).spine ∈ cutAddedEdges A' W O' χ)).card : ℚ)) =
      ∑ i : {T // T ∈ c.typeTwo}, prob i := by
    unfold bitAverage
    simp_rw [natCast_card_filter]
    exact finiteAverage_sum _

  have hevent := book_events_average_le books roots
  obtain ⟨χ, hχ⟩ := exists_le_finiteAverage
    (fun χ : V → Bool => ((cutCover A' W O' χ).card : ℚ))
  have hcover : (transversalNumber (trianglesOn A') : ℚ) ≤ (cutCover A' W O' χ).card := by
    exact_mod_cast (cutCover_covers A' W O' χ).number_le
  have hfour : (4 : ℚ) * transversalNumber (trianglesOn A') ≤
      2 * O'.card + 2 * W.card + 2 * c.typeTwo.card + roots.card := by
    change _ ≤ bitAverage _ at hχ
    linarith
  have hfour_nat : 4 * transversalNumber (trianglesOn c.remainingEdges) ≤
      2 * c.oldRemaining.card + 2 * (TwoLayer.fixedOld c Q).card +
        2 * c.typeTwo.card + roots.card := by
    exact_mod_cast hfour
  have hWcard := TwoLayer.fixedOld_card c hQ
  change 4 * transversalNumber (trianglesOn c.remainingEdges) + 4 * Q.card ≤
    2 * c.oldRemaining.card + 6 * c.typeTwo.card + roots.card
  omega

include hQ in
/-- Helper-arborescence random-cover estimate (`+1/4 h`) in the remaining graph `G'`. -/
theorem remaining_helper_random_cover :
    4 * transversalNumber (trianglesOn c.remainingEdges) + 4 * Q.card ≤
      2 * c.oldRemaining.card + 6 * c.typeTwo.card +
        (privateRedPages c.specialFamily c.newEdges Q).card := by
  have hunrel := remaining_helper_random_cover_unrelaxed c hQ
  have hpriv : (helperRoots c hQ).card ≤ (privateRedPages c.specialFamily c.newEdges Q).card :=
    TwoLayer.oppositeBooks_card_le_privateRed c hQ
  omega

/-- **Unrelaxed Lemma 1.1 (`helper_arborescence_random_cover_unrelaxed`)**: bound `(4'')`
prior to relaxing `|B_out| ≤ h`:
`4 * τ(G) + 4 * |Q| ≤ 6 * n + 10 * a + 6 * b + |B_out|`. -/
theorem helper_arborescence_random_cover_unrelaxed :
    4 * transversalNumber (trianglesOn edges) + 4 * Q.card ≤
      6 * c.initial.card + 10 * c.first.card + 6 * c.typeTwo.card +
        (helperRoots c hQ).card := by
  have hdelete := transversalNumber_le_add_residual
    (trianglesOn edges) (support c.first) (fun _ hT => trianglesOn_nonempty hT)
  rw [← trianglesOn_sdiff] at hdelete
  have hfirst : (support c.first).card = 3 * c.first.card :=
    c.first_packing.card_support_uniform (fun _ hT => trianglesOn_card (c.first_packing.1 hT))
  have hremaining := remaining_helper_random_cover_unrelaxed c hQ
  have hOld := c.oldRemaining_card
  change transversalNumber (trianglesOn edges) ≤
    (support c.first).card + transversalNumber (trianglesOn c.remainingEdges) at hdelete
  omega

include hQ in
/-- **Lemma 1.1 (`helper_arborescence_random_cover`)**: Helper-Arborescence Coupling bound `(4')`:
`4 * τ(G) + 4 * |Q| ≤ 6 * n + 10 * a + 6 * b + h`. -/
theorem helper_arborescence_random_cover :
    4 * transversalNumber (trianglesOn edges) + 4 * Q.card ≤
      6 * c.initial.card + 10 * c.first.card + 6 * c.typeTwo.card +
        (privateRedPages c.specialFamily c.newEdges Q).card := by
  have hunrel := helper_arborescence_random_cover_unrelaxed c hQ
  have hpriv : (helperRoots c hQ).card ≤ (privateRedPages c.specialFamily c.newEdges Q).card :=
    TwoLayer.oppositeBooks_card_le_privateRed c hQ
  omega

end Coupling

end HelperArborescence

namespace Construction

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {edges : Finset (Sym2 V)} (c : Construction edges)

/-- **Unrelaxed Lemma 1.1 (`helper_arborescence_random_cover_unrelaxed`)** (`(4'')`) on `(c, r)`:
`4 * transversalNumber (trianglesOn edges) + 4 * r.second.card ≤
  6 * c.initial.card + 10 * c.first.card + 6 * c.typeTwo.card +
    (HelperArborescence.helperRoots c r.second_maximum.1).card`. -/
theorem helper_arborescence_random_cover_unrelaxed (r : RefinedConstruction c) :
    4 * transversalNumber (trianglesOn edges) + 4 * r.second.card ≤
      6 * c.initial.card + 10 * c.first.card + 6 * c.typeTwo.card +
        (HelperArborescence.helperRoots c r.second_maximum.1).card :=
  HelperArborescence.helper_arborescence_random_cover_unrelaxed c r.second_maximum.1

/-- **Lemma 1.1 (`helper_arborescence_random_cover`)** specialized to `(r : RefinedConstruction c)`:
`4 * transversalNumber (trianglesOn edges) + 4 * r.second.card ≤
  6 * c.initial.card + 10 * c.first.card + 6 * c.typeTwo.card +
    (privateRedPages c.specialFamily c.newEdges r.second).card`. -/
theorem helper_arborescence_random_cover (r : RefinedConstruction c) :
    4 * transversalNumber (trianglesOn edges) + 4 * r.second.card ≤
      6 * c.initial.card + 10 * c.first.card + 6 * c.typeTwo.card +
        (privateRedPages c.specialFamily c.newEdges r.second).card :=
  HelperArborescence.helper_arborescence_random_cover c r.second_maximum.1

end Construction

end TuzaBound
