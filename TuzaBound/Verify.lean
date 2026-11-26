/-
Copyright (c) 2026 Tyler B. Hughes. All rights reserved.
Released under MIT license as described in the file LICENSE.
Kernel axiom and type-signature audit for `TuzaBound`.
-/
module

public import TuzaBound

/-!
# Kernel Type and Axiom Verification Audit for `TuzaBound`

Verifies via `#check` and `#print axioms` that every public definition, structural lemma,
intermediate cover bound, main theorem (`29 * tau G ≤ 81 * nu G`), non-vacuity witness
on `K_4`, and Theorem 2(a) fixed-point recurrence in `TuzaBound` compiles cleanly and depends ONLY
on Lean 4's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`) — NEVER `sorryAx`,
`Lean.ofReduceBool`, `Lean.trustCompiler`, or any custom axiom.
-/

-- 1. Graph Definitions, Equivalence Lemmas, and Non-Vacuity Witnesses on K_4 (Graph.lean, Main.lean)
#check @TuzaBound.nu
#check @TuzaBound.tau
#check @TuzaBound.graphEdges
#check @TuzaBound.graphTriangles
#check @TuzaBound.mem_graphTriangles_iff
#check @TuzaBound.triangleEdges_mem_graphTriangles_iff
#check @TuzaBound.graph_trivial_bound
#check @TuzaBound.graph_cover_iff_adj
#check @TuzaBound.exists_graph_minimumCover
#check @TuzaBound.tau_le_iff
#check @TuzaBound.le_nu_iff
#check @TuzaBound.complete4_triangles_not_disjoint
#check @TuzaBound.nu_complete4
#check @TuzaBound.tau_complete4

#print axioms TuzaBound.nu
#print axioms TuzaBound.tau
#print axioms TuzaBound.graphEdges
#print axioms TuzaBound.graphTriangles
#print axioms TuzaBound.mem_graphTriangles_iff
#print axioms TuzaBound.triangleEdges_mem_graphTriangles_iff
#print axioms TuzaBound.graph_trivial_bound
#print axioms TuzaBound.graph_cover_iff_adj
#print axioms TuzaBound.exists_graph_minimumCover
#print axioms TuzaBound.tau_le_iff
#print axioms TuzaBound.le_nu_iff
#print axioms TuzaBound.complete4_triangles_not_disjoint
#print axioms TuzaBound.nu_complete4
#print axioms TuzaBound.tau_complete4

-- 2. Packings, Covers, Triangle Geometry, Coloring, and Arithmetic (Basic/*)
#check @TuzaBound.IsPacking
#check @TuzaBound.IsMaximumPacking
#check @TuzaBound.IsLexMaximumPacking
#check @TuzaBound.IsCover
#check @TuzaBound.packingNumber
#check @TuzaBound.transversalNumber
#check @TuzaBound.IsMaximumPacking.no_two_for_one
#check @TuzaBound.two_page_triangle
#check @TuzaBound.two_page_opposite_mem
#check @TuzaBound.three_page_spine
#check @TuzaBound.second_colored_cover
#check @TuzaBound.colored_bound_arithmetic
#check @TuzaBound.colored_refined_arithmetic
#check @TuzaBound.four_bounds_arithmetic
#check @TuzaBound.five_bounds_arithmetic
#check @TuzaBound.five_bounds_arithmetic_250_699
#check @TuzaBound.six_bounds_arithmetic_29_81
#check @TuzaBound.six_bounds_arithmetic_29_81_simple

#print axioms TuzaBound.IsMaximumPacking.no_two_for_one
#print axioms TuzaBound.two_page_triangle
#print axioms TuzaBound.two_page_opposite_mem
#print axioms TuzaBound.three_page_spine
#print axioms TuzaBound.second_colored_cover
#print axioms TuzaBound.colored_bound_arithmetic
#print axioms TuzaBound.colored_refined_arithmetic
#print axioms TuzaBound.four_bounds_arithmetic
#print axioms TuzaBound.five_bounds_arithmetic
#print axioms TuzaBound.five_bounds_arithmetic_250_699
#print axioms TuzaBound.six_bounds_arithmetic_29_81
#print axioms TuzaBound.six_bounds_arithmetic_29_81_simple

-- 3. Books and Colored Exchange / Covers (Books/*, Colored/*)
#check @TuzaBound.Book.meets_cover
#check @TuzaBound.exists_cover_of_small_common_spine_books
#check @TuzaBound.unique_residual_triangle
#check @TuzaBound.exists_first_colored_cover
#check @TuzaBound.first_colored_cover
#check @TuzaBound.colored_bound
#check @TuzaBound.recursive_colored_cover
#check @TuzaBound.colored_refined

#print axioms TuzaBound.Book.meets_cover
#print axioms TuzaBound.exists_cover_of_small_common_spine_books
#print axioms TuzaBound.unique_residual_triangle
#print axioms TuzaBound.exists_first_colored_cover
#print axioms TuzaBound.first_colored_cover
#print axioms TuzaBound.colored_bound
#print axioms TuzaBound.recursive_colored_cover
#print axioms TuzaBound.colored_refined

-- 4. Finite Boolean Averages, Random Cuts, and Arborescence Combinatorics (Probability/*)
#check @TuzaBound.finiteAverage
#check @TuzaBound.bitAverage
#check @TuzaBound.exists_le_finiteAverage
#check @TuzaBound.bitAverage_restrict
#check @TuzaBound.allConstColor_average
#check @TuzaBound.sameColor_average
#check @TuzaBound.spineEvent_average
#check @TuzaBound.bookEvent_average
#check @TuzaBound.cutCover_covers
#check @TuzaBound.selectedOld_average
#check @TuzaBound.cutAddedEdges_book_witness
#check @TuzaBound.random_book_cover
#check @TuzaBound.Arborescence.reachIn_sink_unique
#check @TuzaBound.Arborescence.exists_chain_from_sink
#check @TuzaBound.Arborescence.basin_disjoint
#check @TuzaBound.Arborescence.biUnion_childrenOf_eq_erase
#check @TuzaBound.Arborescence.sum_childrenOf_card
#check @TuzaBound.Arborescence.fourth_pow_secant
#check @TuzaBound.Arborescence.basin_prob_sum_le
#check @TuzaBound.Arborescence.global_prob_sum_le

#print axioms TuzaBound.exists_le_finiteAverage
#print axioms TuzaBound.bitAverage_restrict
#print axioms TuzaBound.allConstColor_average
#print axioms TuzaBound.sameColor_average
#print axioms TuzaBound.spineEvent_average
#print axioms TuzaBound.bookEvent_average
#print axioms TuzaBound.cutCover_covers
#print axioms TuzaBound.selectedOld_average
#print axioms TuzaBound.cutAddedEdges_book_witness
#print axioms TuzaBound.random_book_cover
#print axioms TuzaBound.Arborescence.reachIn_sink_unique
#print axioms TuzaBound.Arborescence.exists_chain_from_sink
#print axioms TuzaBound.Arborescence.basin_disjoint
#print axioms TuzaBound.Arborescence.biUnion_childrenOf_eq_erase
#print axioms TuzaBound.Arborescence.sum_childrenOf_card
#print axioms TuzaBound.Arborescence.fourth_pow_secant
#print axioms TuzaBound.Arborescence.basin_prob_sum_le
#print axioms TuzaBound.Arborescence.global_prob_sum_le

-- 5. Haxell–Wang Construction, Lemma 1.2 (Unmerged Covers), and Lemma 1.1 (Helper Arborescence)
#check @TuzaBound.exists_construction
#check @TuzaBound.exists_refinedConstruction
#check @TuzaBound.Construction.first_cover
#check @TuzaBound.Construction.full_book_cover
#check @TuzaBound.Construction.exists_unmerged_cover_6a
#check @TuzaBound.Construction.exists_unmerged_cover_6b
#check @TuzaBound.Construction.exists_unmerged_cover_6c
#check @TuzaBound.Construction.unmerged_cover_6a
#check @TuzaBound.Construction.unmerged_cover_6b
#check @TuzaBound.Construction.unmerged_cover_6c
#check @TuzaBound.Construction.unmerged_colored_covers
#check @TuzaBound.Construction.elementary_colored_covers
#check @TuzaBound.Construction.fourth_cover
#check @TuzaBound.TwoLayer.random_cover
#check @TuzaBound.HelperArborescence.exists_disjoint_spokes
#check @TuzaBound.HelperArborescence.spine_injective
#check @TuzaBound.HelperArborescence.helperNext_eq_some_iff
#check @TuzaBound.HelperArborescence.helperNext_eq_none_of_roots
#check @TuzaBound.HelperArborescence.cand_properties
#check @TuzaBound.HelperArborescence.basin_third_vertex_child
#check @TuzaBound.HelperArborescence.spine_prob_le_in_basin
#check @TuzaBound.HelperArborescence.remaining_helper_random_cover_unrelaxed
#check @TuzaBound.HelperArborescence.remaining_helper_random_cover
#check @TuzaBound.HelperArborescence.helper_arborescence_random_cover_unrelaxed
#check @TuzaBound.HelperArborescence.helper_arborescence_random_cover
#check @TuzaBound.Construction.helper_arborescence_random_cover_unrelaxed
#check @TuzaBound.Construction.helper_arborescence_random_cover
#check @TuzaBound.IsLexMaximumPacking.no_one_to_two
#check @TuzaBound.IsLexMaximumPacking.no_two_to_three
#check @TuzaBound.OppositeElimination.rootPages_subset_privPages
#check @TuzaBound.OppositeElimination.rootPages_card_eq
#check @TuzaBound.OppositeElimination.helperRoots_add_privZeroPages_card
#check @TuzaBound.OppositeElimination.step3_nonprivate_obstruction
#check @TuzaBound.OppositeElimination.step4_bout_obstruction
#check @TuzaBound.OppositeElimination.remainingCoreCover_covers
#check @TuzaBound.Construction.helperRoots_add_privZeroPages_card
#check @TuzaBound.Construction.exists_opposite_elimination_cover
#check @TuzaBound.Construction.opposite_elimination_cover

#print axioms TuzaBound.exists_construction
#print axioms TuzaBound.exists_refinedConstruction
#print axioms TuzaBound.Construction.first_cover
#print axioms TuzaBound.Construction.full_book_cover
#print axioms TuzaBound.Construction.exists_unmerged_cover_6a
#print axioms TuzaBound.Construction.exists_unmerged_cover_6b
#print axioms TuzaBound.Construction.exists_unmerged_cover_6c
#print axioms TuzaBound.Construction.unmerged_cover_6a
#print axioms TuzaBound.Construction.unmerged_cover_6b
#print axioms TuzaBound.Construction.unmerged_cover_6c
#print axioms TuzaBound.Construction.unmerged_colored_covers
#print axioms TuzaBound.Construction.elementary_colored_covers
#print axioms TuzaBound.Construction.fourth_cover
#print axioms TuzaBound.TwoLayer.random_cover
#print axioms TuzaBound.HelperArborescence.exists_disjoint_spokes
#print axioms TuzaBound.HelperArborescence.spine_injective
#print axioms TuzaBound.HelperArborescence.helperNext_eq_some_iff
#print axioms TuzaBound.HelperArborescence.helperNext_eq_none_of_roots
#print axioms TuzaBound.HelperArborescence.cand_properties
#print axioms TuzaBound.HelperArborescence.basin_third_vertex_child
#print axioms TuzaBound.HelperArborescence.spine_prob_le_in_basin
#print axioms TuzaBound.HelperArborescence.remaining_helper_random_cover_unrelaxed
#print axioms TuzaBound.HelperArborescence.remaining_helper_random_cover
#print axioms TuzaBound.HelperArborescence.helper_arborescence_random_cover_unrelaxed
#print axioms TuzaBound.HelperArborescence.helper_arborescence_random_cover
#print axioms TuzaBound.Construction.helper_arborescence_random_cover_unrelaxed
#print axioms TuzaBound.Construction.helper_arborescence_random_cover
#print axioms TuzaBound.IsLexMaximumPacking.no_one_to_two
#print axioms TuzaBound.IsLexMaximumPacking.no_two_to_three
#print axioms TuzaBound.OppositeElimination.rootPages_subset_privPages
#print axioms TuzaBound.OppositeElimination.rootPages_card_eq
#print axioms TuzaBound.OppositeElimination.helperRoots_add_privZeroPages_card
#print axioms TuzaBound.OppositeElimination.step3_nonprivate_obstruction
#print axioms TuzaBound.OppositeElimination.step4_bout_obstruction
#print axioms TuzaBound.OppositeElimination.remainingCoreCover_covers
#print axioms TuzaBound.Construction.helperRoots_add_privZeroPages_card
#print axioms TuzaBound.Construction.exists_opposite_elimination_cover
#print axioms TuzaBound.Construction.opposite_elimination_cover

-- 6. Main Theorems: 29 * τ(G) ≤ 81 * ν(G), 250 * τ(G) ≤ 699 * ν(G), and Wang (Main.lean)
#check @TuzaBound.Construction.four_covers
#check @TuzaBound.Construction.five_covers
#check @TuzaBound.Construction.six_covers_81_29
#check @TuzaBound.Construction.bound_with_private_slack
#check @TuzaBound.Construction.bound_with_residual
#check @TuzaBound.Construction.bound_81_29_with_slack
#check @TuzaBound.Construction.bound_81_29
#check @TuzaBound.triangles_bound
#check @TuzaBound.triangles_bound_81_29
#check @TuzaBound.tuza_bound_nat
#check @TuzaBound.tuza_bound
#check @TuzaBound.exists_small_triangle_transversal
#check @TuzaBound.tuza_bound_81_29_nat
#check @TuzaBound.tuza_bound_81_29
#check @TuzaBound.exists_small_triangle_transversal_81_29
#check @TuzaBound.bound_699_250_from_81_29
#check @TuzaBound.wang_bound_from_699_250

#print axioms TuzaBound.Construction.four_covers
#print axioms TuzaBound.Construction.five_covers
#print axioms TuzaBound.Construction.six_covers_81_29
#print axioms TuzaBound.Construction.bound_with_private_slack
#print axioms TuzaBound.Construction.bound_with_residual
#print axioms TuzaBound.Construction.bound_81_29_with_slack
#print axioms TuzaBound.Construction.bound_81_29
#print axioms TuzaBound.triangles_bound
#print axioms TuzaBound.triangles_bound_81_29
#print axioms TuzaBound.tuza_bound_nat
#print axioms TuzaBound.tuza_bound
#print axioms TuzaBound.exists_small_triangle_transversal
#print axioms TuzaBound.tuza_bound_81_29_nat
#print axioms TuzaBound.tuza_bound_81_29
#print axioms TuzaBound.exists_small_triangle_transversal_81_29
#print axioms TuzaBound.bound_699_250_from_81_29
#print axioms TuzaBound.wang_bound_from_699_250

-- 7. Theorem 2(a): Algebraic (8/3, 2/3) Fixed-Point Recurrence & Infinite-Depth LP Invariance
#check @TuzaBound.book2_le_book3
#check @TuzaBound.fixed_point_recurrence_eq
#check @TuzaBound.fixed_point_recurrence
#check @TuzaBound.IsValidInfiniteHierarchyPoint
#check @TuzaBound.infinite_depth_lp_upper
#check @TuzaBound.infinite_depth_lp_attained
#check @TuzaBound.infinite_depth_lp_exact_699_250

#print axioms TuzaBound.book2_le_book3
#print axioms TuzaBound.fixed_point_recurrence_eq
#print axioms TuzaBound.fixed_point_recurrence
#print axioms TuzaBound.infinite_depth_lp_upper
#print axioms TuzaBound.infinite_depth_lp_attained
#print axioms TuzaBound.infinite_depth_lp_exact_699_250
