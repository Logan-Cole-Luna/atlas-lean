/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Percolation.Universality.RotatedDualCounterexamples
public import Mathlib.Tactic

/-!
# Tests for `MathlibExt.Probability.Percolation.Universality.RotatedDualCounterexamples`

* The refutations: the same-box dichotomy with the rotated dual is false
  (`bcc_dichotomy_false`, witness `bcc_wallCfg`: `bcc_wall_noH_noV`), and the hypothesis of
  the former `dcw_square_dichotomy` is false for `n = 2` and `n = 5`
  (`bcc_square_dichotomy_hyp_false`).
* `bcc_wallCfg` evaluated on a wall edge and a non-wall edge; `bcc_dualVert_botCfg`;
  `bcc_dualReach_separates` for the wall configuration.
* The rotated crossing is not the crossing on the shifted dual lattice: `bcc_wallCfg` has a
  `DualVerticalCrossing` of `[0, 2]²` through the faces with lower-left corners `(0, 0)`,
  `(0, 1)` and `(0, 2)`, while `bcc_noV_wall` rules out a crossing in `dualConfig bcc_wallCfg`.
-/

@[expose] public section

open StatMech StatMech.Lattice StatMech.RSW.Box StatMech.Universality SimpleGraph

namespace MathlibExtTest.StatMech.Probability.Percolation.Universality.RotatedDualCounterexamples

example : bcc_wallCfg s(![0, 1], ![1, 1]) = false := (bcc_wallCfg_false_iff _).2 (Or.inr (Or.inl rfl))

example : bcc_wallCfg s(![1, 0], ![2, 0]) = true := by
  decide

example : ¬ ((horizontalCrossingEvent 0 2 0 2)ᶜ ⊆ dualConfig ⁻¹' verticalCrossingEvent 0 2 0 2) :=
  bcc_dichotomy_false

example : ¬ HorizontalCrossing bcc_wallCfg 0 2 0 2 ∧
    ¬ VerticalCrossing (dualConfig bcc_wallCfg) 0 2 0 2 :=
  bcc_wall_noH_noV

/-- The wall configuration has a bottom–top crossing of `[0, 2]²` on the shifted dual lattice: the
faces with lower-left corners `(0, 0)`, `(0, 1)` and `(0, 2)` are joined across the closed wall
bonds at heights `1` and `2`. Its rotated complement has no crossing of the same box. -/
example : DualVerticalCrossing bcc_wallCfg 0 2 0 2 ∧
    ¬ VerticalCrossing (dualConfig bcc_wallCfg) 0 2 0 2 := by
  refine ⟨?_, bcc_noV_wall⟩
  have hr : ∀ b : ℤ, 0 ≤ b → b ≤ 2 → (![0, b] : Site 2) ∈ rect 0 2 0 2 := fun b h0 h2 => by
    simp [mem_rect, h0, h2]
  have step : ∀ (b : ℤ) (h0 : 0 ≤ b) (h1 : b ≤ 1),
      bcc_wallCfg s(![0, b + 1], ![0 + 1, b + 1]) = false →
      Relation.ReflTransGen (fun f g : rect 0 2 0 2 =>
          dualLattice.Adj f g ∧ bcc_wallCfg (sharedPrimalEdge f g) = false)
        ⟨![0, b], hr b h0 (by omega)⟩ ⟨![0, b + 1], hr (b + 1) (by omega) (by omega)⟩ :=
    fun b _ _ hcl => Relation.ReflTransGen.single
      ⟨latAdj_top 0 b, by rw [sharedPrimalEdge_top]; exact hcl⟩
  rw [dualVerticalCrossing_iff]
  refine ⟨⟨![0, 0], hr 0 le_rfl (by norm_num), by simp⟩,
    ⟨![0, 2], hr 2 (by norm_num) le_rfl, by simp⟩, ?_⟩
  exact (step 0 le_rfl (by norm_num) (by decide)).trans (step 1 (by norm_num) le_rfl (by decide))

example : ¬ ∀ ω : ConfigSpace (Sym2 (Site 2)), ¬ HorizontalCrossing ω 0 5 0 5 → dcw_BarrierRoute ω 5 :=
  bcc_square_dichotomy_hyp_false 5 (by norm_num)

example : VerticalCrossing (dualConfig bcc_botCfg) 0 2 0 2 := bcc_dualVert_botCfg

example : ¬ (latticeMinusBarrier (bcc_dualBottomReach bcc_wallCfg 2)).Reachable ![0, 0] ![0, 2] :=
  bcc_dualReach_separates _ 2 bcc_noV_wall (by simp [bottomSide]) (by simp [topSide])

end MathlibExtTest.StatMech.Probability.Percolation.Universality.RotatedDualCounterexamples
