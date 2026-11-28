/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.PublicKey.Assumptions.LWE

/-!
# Tests for learning with errors

Two tests over `ZMod 2` follow the error term: with two entries the error vector is `(1, 1)`
with probability `χ(1)²`, and in dimension `0` with one sample and coins in `Unit` the real
experiment shows the error itself. With the error distribution `χ = PMF.pure 0` (no errors) and
any modulus `q ≥ 1`, the error vector is `0`, and for coins uniform in any finite nonempty type
the search and real experiments run the adversary on `(A, A s)`. The examples below show that
both LWE problems are then easy for the parameters they state, all with coins in `Unit`:
* search: over `ZMod 3` with `n = m = 1`, the solver `(a, b) ↦ a b` (which is `a⁻¹ b` for
  `a ≠ 0`) recovers `s` with probability `7/9`, above the `1/3` of a guess;
* decision: over `ZMod 2` with `m = n + 1`, the distinguisher "is `b` in the image of `A`?"
  outputs `1` on every real sample and with probability at most `1/2` on random ones, so its
  advantage is at least `1/2` in every dimension `n`, and `DecisionLWE` with `q(n) = 2` and
  `m(n) = n + 1` fails for the class of all distinguisher families: the assumption is not
  vacuous.

A constant distinguisher has advantage `0` for all parameters and every finite nonempty coin type,
so `DecisionLWE` with `q(n) = 2`, `m(n) = n + 1`, no errors and coins in `Unit` holds for the class
of constant families: the assumption can hold.
-/

@[expose] public section

namespace Cslib.Crypto.PublicKey.Assumptions.LWETests

open Finset Cslib.Crypto.Framework Cslib.Crypto.PublicKey.Assumptions
open Cslib.Probability.PMF (uniformOfFintype)
open scoped Matrix

/-- For a modulus `q ≥ 1` and every number `m` of samples, without errors the error vector is
`0`. -/
theorem lweErrors_pure_zero {q : ℕ} [NeZero q] (m : ℕ) :
    lweErrors (PMF.pure (0 : ZMod q)) m = PMF.pure 0 := by
  ext e
  simp only [lweErrors, PMF.ofFintype_apply, PMF.pure_apply]
  by_cases he : e = 0
  · simp [he]
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp he
    rw [ite_eq_right he]
    exact prod_eq_zero (mem_univ i) (ite_eq_right hi)

/-- A game that ignores its sample has the constant outcome. -/
private theorem map_const' {α : Type*} (p : PMF α) (b : Bool) : p.map (fun _ => b) = PMF.pure b :=
  PMF.map_const p b

/-- For a modulus `q ≥ 1` and coins uniform in a finite nonempty type `S`, without errors the
search experiment tests the solver on `(A, A s)`. -/
theorem lweSearchGame_pure_zero {n m q : ℕ} [NeZero q] {S : Type*} [Fintype S] [Nonempty S]
    (F : Matrix (Fin m) (Fin n) (ZMod q) → (Fin m → ZMod q) → S → Fin n → ZMod q) :
    lweSearchGame (PMF.pure 0) F = (uniformOfFintype _).map fun ω :
      Matrix (Fin m) (Fin n) (ZMod q) × (Fin n → ZMod q) × S =>
        decide (F ω.1 (ω.1 *ᵥ ω.2.1) ω.2.2 = ω.2.1) := by
  simp only [lweSearchGame, lweErrors_pure_zero, PMF.pure_map, add_zero]
  exact PMF.bind_pure_comp _ _

/-- For a modulus `q ≥ 1` and coins uniform in a finite nonempty type `S`, without errors the
real decision experiment runs the distinguisher on `(A, A s)`. -/
theorem lweReal_pure_zero {n m q : ℕ} [NeZero q] {S : Type*} [Fintype S] [Nonempty S]
    (D : Matrix (Fin m) (Fin n) (ZMod q) → (Fin m → ZMod q) → S → Bool) :
    lweReal (PMF.pure 0) D = (uniformOfFintype _).map fun ω :
      Matrix (Fin m) (Fin n) (ZMod q) × (Fin n → ZMod q) × S => D ω.1 (ω.1 *ᵥ ω.2.1) ω.2.2 := by
  simp only [lweReal, lweErrors_pure_zero, PMF.pure_map, add_zero]
  exact PMF.bind_pure_comp _ _

/-! ### The error term -/

/-- Over `ZMod 2`, with two entries, the error vector is `(1, 1)` with probability `χ(1)²`. -/
example (χ : PMF (ZMod 2)) : lweErrors χ 2 ![1, 1] = χ 1 ^ 2 := by
  simp [lweErrors, Fin.prod_univ_two, sq]

/-- Over `ZMod 2`, in dimension `0` with one sample and coins in `Unit`, the real experiment
shows the error itself: the distinguisher that tests `b = 1` outputs `1` with probability
`χ(1)`. -/
example (χ : PMF (ZMod 2)) :
    winProb (lweReal χ fun (_ : Matrix (Fin 1) (Fin 0) (ZMod 2)) (b : Fin 1 → ZMod 2) (_ : Unit) =>
      decide (b 0 = 1)) = (χ 1).toReal := by
  simp only [lweReal, winProb, PMF.bind_apply, PMF.map_apply, tsum_fintype]
  simp [lweErrors, Cslib.Probability.PMF.uniformOfFintype_apply, Fintype.card_unique]
  rw [← (Equiv.funUnique (Fin 1) (ZMod 2)).symm.sum_comp]
  simp

/-! ### Search -/

/-- The solver `(a, b) ↦ a b` for `n = m = 1` over `ZMod 3`, with coins in `Unit`: since
`a² = 1` for `a ≠ 0`, it outputs `a⁻¹ b`. -/
def solver : Matrix (Fin 1) (Fin 1) (ZMod 3) → (Fin 1 → ZMod 3) → Unit → Fin 1 → ZMod 3 :=
  fun A b _ _ => A 0 0 * b 0

/-- **Non-vacuity of search LWE.** Over `ZMod 3` with `n = m = 1` and without errors, the solver
wins on the `6` samples with `a ≠ 0` and on the `1` with `a = 0` and `s = 0`: its advantage is
`7/9`. -/
example : lweSearchAdvantage (PMF.pure 0) solver = 7 / 9 := by
  rw [lweSearchAdvantage, lweSearchGame_pure_zero, winProb_map_uniform]
  have hcard : Fintype.card (Matrix (Fin 1) (Fin 1) (ZMod 3) × (Fin 1 → ZMod 3) × Unit) = 9 :=
    rfl
  have hwin : (univ.filter fun ω : Matrix (Fin 1) (Fin 1) (ZMod 3) × (Fin 1 → ZMod 3) × Unit =>
      decide (solver ω.1 (ω.1 *ᵥ ω.2.1) ω.2.2 = ω.2.1) = true).card = 7 := by
    decide
  rw [hcard, hwin]
  norm_num

/-! ### Decision -/

/-- For all `n`, `m`, a modulus `q ≥ 1`, an error distribution `χ` and coins in a finite
nonempty type `S`, a constant distinguisher has decision LWE advantage `0`. -/
example {n m q : ℕ} [NeZero q] {S : Type*} [Fintype S] [Nonempty S] (χ : PMF (ZMod q))
    (b : Bool) :
    lweAdvantage χ (fun (_ : Matrix (Fin m) (Fin n) (ZMod q)) (_ : Fin m → ZMod q) (_ : S) => b) =
      0 := by
  simp [lweAdvantage, lweReal, lweRand, advantage, map_const']

/-- For an `(n + 1) × n` matrix `A` over `ZMod 2` and coins in `Unit`, the distinguisher that
outputs `1` when `b` is in the image of `A`. -/
def inRange (n : ℕ) :
    Matrix (Fin (n + 1)) (Fin n) (ZMod 2) → (Fin (n + 1) → ZMod 2) → Unit → Bool :=
  fun A b _ => decide (∃ s, A *ᵥ s = b)

/-- Over `ZMod 2` with `m = n + 1` and without errors, `inRange n` has decision LWE advantage at
least `1/2`: it outputs `1` on every real sample, and on a random one with probability at most
`1/2`, because the image of `A` has at most `2 ^ n` of the `2 ^ (n + 1)` vectors. -/
theorem half_le_lweAdvantage_inRange (n : ℕ) :
    1 / 2 ≤ lweAdvantage (PMF.pure (0 : ZMod 2)) (inRange n) := by
  classical
  have hreal : winProb (lweReal (PMF.pure 0) (inRange n)) = 1 := by
    rw [lweReal_pure_zero]
    have : (fun ω : Matrix (Fin (n + 1)) (Fin n) (ZMod 2) × (Fin n → ZMod 2) × Unit =>
        inRange n ω.1 (ω.1 *ᵥ ω.2.1) ω.2.2) = fun _ => true := by
      funext ω
      simp [inRange]
    rw [this, map_const', winProb_pure, ite_eq_left rfl]
  have hsub : (univ.filter fun ω : Matrix (Fin (n + 1)) (Fin n) (ZMod 2) ×
      (Fin (n + 1) → ZMod 2) × Unit => inRange n ω.1 ω.2.1 ω.2.2 = true) ⊆
      univ.image fun ω : Matrix (Fin (n + 1)) (Fin n) (ZMod 2) × (Fin n → ZMod 2) × Unit =>
        (ω.1, ω.1 *ᵥ ω.2.1, ω.2.2) := by
    rintro ⟨A, b, c⟩ h
    obtain ⟨s, hs⟩ := by simpa [inRange] using h
    exact mem_image.mpr ⟨(A, s, c), mem_univ _, by simp [hs]⟩
  have hcount := (card_le_card hsub).trans card_image_le
  rw [card_univ] at hcount
  have hrand : winProb (lweRand (inRange n)) ≤ 1 / 2 := by
    rw [lweRand, winProb_map_uniform]
    set M := Fintype.card (Matrix (Fin (n + 1)) (Fin n) (ZMod 2))
    have hM : (0 : ℝ) < M := by exact_mod_cast Fintype.card_pos
    simp only [Fintype.card_prod, Fintype.card_fun, ZMod.card, Fintype.card_fin,
      Fintype.card_unit, mul_one] at hcount ⊢
    have hcount' : ((univ.filter fun ω : Matrix (Fin (n + 1)) (Fin n) (ZMod 2) ×
        (Fin (n + 1) → ZMod 2) × Unit => inRange n ω.1 ω.2.1 ω.2.2 = true).card : ℝ) ≤
        M * 2 ^ n := by exact_mod_cast hcount
    rw [div_le_iff₀ (by positivity)]
    push_cast
    nlinarith [pow_succ (2 : ℝ) n]
  rw [lweAdvantage, advantage, hreal]
  rw [abs_of_nonneg (by linarith [winProb_le_one (lweRand (inRange n))])]
  linarith

/-- **Non-vacuity of the decision LWE assumption.** Without errors, with `m n = n + 1`,
`q n = 2` and coins in `Unit`, the decision LWE assumption fails for the class of all
distinguisher families: the family `inRange` has advantage at least `1/2` in every dimension. -/
example : ¬ DecisionLWE (fun n => n + 1) (fun _ => 2) ⟨Polynomial.X + 1, fun n => by simp⟩
    ⟨Polynomial.C 2, fun n => by simp⟩ (fun _ => PMF.pure 0) (fun _ => Unit) (fun _ => True) :=
  fun h => not_negligibleAdv_const (by norm_num : (0 : ℝ) < 1 / 2)
    ((h inRange trivial).mono half_le_lweAdvantage_inRange)

/-- Without errors, with `m n = n + 1`, `q n = 2` and coins in `Unit`, the decision LWE
assumption holds for the class of constant distinguisher families, whose advantage is `0`. -/
example : DecisionLWE (fun n => n + 1) (fun _ => 2) ⟨Polynomial.X + 1, fun n => by simp⟩
    ⟨Polynomial.C 2, fun n => by simp⟩ (fun _ => PMF.pure 0) (fun _ => Unit)
    (fun D => ∀ n, ∃ b, D n = fun _ _ _ => b) := by
  intro D hD
  refine negligibleAdv_zero.mono fun n => ?_
  obtain ⟨b, hb⟩ := hD n
  simp [hb, lweAdvantage, lweReal, lweRand, advantage, map_const']

end Cslib.Crypto.PublicKey.Assumptions.LWETests
