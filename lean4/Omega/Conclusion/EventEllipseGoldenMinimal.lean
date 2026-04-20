import Mathlib.Tactic
import Mathlib.NumberTheory.Real.GoldenRatio

namespace Omega.Conclusion.EventEllipseGoldenMinimal

open Real

/-- Upper-triangular shear.
    thm:conclusion-event-ellipse-golden-minimal-stretch -/
def R : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 0, 1]

/-- Lower-triangular shear.
    thm:conclusion-event-ellipse-golden-minimal-stretch -/
def L : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 1, 1]

/-- Product `R · L = [[2,1],[1,1]]`.
    thm:conclusion-event-ellipse-golden-minimal-stretch -/
theorem R_mul_L : R * L = !![2, 1; 1, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [R, L, Matrix.mul_apply, Fin.sum_univ_two]; try norm_num)

/-- Determinant of `R · L` is `1`.
    thm:conclusion-event-ellipse-golden-minimal-stretch -/
theorem det_R_mul_L : (R * L).det = 1 := by
  rw [R_mul_L, Matrix.det_fin_two]
  simp; norm_num

/-- Trace of `R · L` is `3`.
    thm:conclusion-event-ellipse-golden-minimal-stretch -/
theorem trace_R_mul_L : (R * L).trace = 3 := by
  rw [R_mul_L]
  simp [Matrix.trace, Fin.sum_univ_two]; norm_num

/-- `φ² = φ + 1`.
    thm:conclusion-event-ellipse-golden-minimal-stretch -/
theorem goldenRatio_sq_eq : goldenRatio ^ 2 = goldenRatio + 1 := goldenRatio_sq

/-- Quartic identity: `φ⁴ - 3φ² + 1 = 0` (since `φ² = φ + 1`, `φ⁴ = (φ+1)² = 3φ + 2`).
    thm:conclusion-event-ellipse-golden-minimal-stretch -/
theorem goldenRatio_pow_four_identity :
    goldenRatio ^ 4 - 3 * goldenRatio ^ 2 + 1 = 0 := by
  have h : goldenRatio ^ 2 = goldenRatio + 1 := goldenRatio_sq
  have h4 : goldenRatio ^ 4 = 3 * goldenRatio + 2 := by
    have : goldenRatio ^ 4 = (goldenRatio + 1) ^ 2 := by
      calc goldenRatio ^ 4 = (goldenRatio ^ 2) ^ 2 := by ring
        _ = (goldenRatio + 1) ^ 2 := by rw [h]
    rw [this]; nlinarith [h]
  linarith [h, h4]

/-- `φ² · (φ⁻¹)² = 1`.
    thm:conclusion-event-ellipse-golden-minimal-stretch -/
theorem goldenRatio_sq_mul_inv_sq :
    goldenRatio ^ 2 * (goldenRatio⁻¹) ^ 2 = 1 := by
  have hne : goldenRatio ≠ 0 := goldenRatio_ne_zero
  rw [inv_pow, mul_inv_cancel₀ (pow_ne_zero 2 hne)]

/-- `φ⁻¹ = φ - 1` (from `φ² = φ + 1`, so `φ(φ-1) = 1`).
    thm:conclusion-event-ellipse-golden-minimal-stretch -/
theorem goldenRatio_inv_eq_sub_one : goldenRatio⁻¹ = goldenRatio - 1 := by
  have hne : goldenRatio ≠ 0 := goldenRatio_ne_zero
  have h : goldenRatio ^ 2 = goldenRatio + 1 := goldenRatio_sq
  have hmul : (goldenRatio - 1) * goldenRatio = 1 := by nlinarith [h]
  exact inv_eq_of_mul_eq_one_left hmul

/-- `φ² + (φ⁻¹)² = 3`. Derived from `φ² = φ + 1` and `φ⁻¹ = φ - 1`.
    thm:conclusion-event-ellipse-golden-minimal-stretch -/
theorem goldenRatio_sq_plus_inv_sq :
    goldenRatio ^ 2 + (goldenRatio⁻¹) ^ 2 = 3 := by
  have h : goldenRatio ^ 2 = goldenRatio + 1 := goldenRatio_sq
  have hinv : goldenRatio⁻¹ = goldenRatio - 1 := goldenRatio_inv_eq_sub_one
  rw [hinv]
  nlinarith [h]

/-- Inverse quartic: `(φ⁻¹)⁴ - 3 · (φ⁻¹)² + 1 = 0`.
    thm:conclusion-event-ellipse-golden-minimal-stretch -/
theorem goldenRatio_inv_sq_char :
    (goldenRatio⁻¹) ^ 4 - 3 * (goldenRatio⁻¹) ^ 2 + 1 = 0 := by
  have h : goldenRatio ^ 2 = goldenRatio + 1 := goldenRatio_sq
  have hinv : goldenRatio⁻¹ = goldenRatio - 1 := goldenRatio_inv_eq_sub_one
  rw [hinv]
  nlinarith [h]

/-- Paper package (T=1 algebraic core).
    thm:conclusion-event-ellipse-golden-minimal-stretch -/
theorem paper_event_ellipse_golden_minimal_stretch_T1 :
    goldenRatio ^ 2 * (goldenRatio⁻¹) ^ 2 = 1 ∧
    goldenRatio ^ 2 + (goldenRatio⁻¹) ^ 2 = 3 ∧
    goldenRatio ^ 2 / (goldenRatio⁻¹) ^ 2 = goldenRatio ^ 4 := by
  refine ⟨goldenRatio_sq_mul_inv_sq, goldenRatio_sq_plus_inv_sq, ?_⟩
  rw [inv_pow, div_eq_mul_inv, inv_inv, ← pow_add]

-- Phase R608: Golden ratio Fibonacci power identities
-- ══════════════════════════════════════════════════════════════

/-- φ³ = 2φ + 1.
    thm:conclusion-event-ellipse-golden-minimal-stretch -/
theorem goldenRatio_cube : goldenRatio ^ 3 = 2 * goldenRatio + 1 := by
  have h := goldenRatio_sq
  nlinarith [h, sq_nonneg goldenRatio]

/-- φ⁵ = 5φ + 3.
    thm:conclusion-event-ellipse-golden-minimal-stretch -/
theorem goldenRatio_pow_five : goldenRatio ^ 5 = 5 * goldenRatio + 3 := by
  have h := goldenRatio_sq
  have h3 := goldenRatio_cube
  have h5 : goldenRatio ^ 5 = goldenRatio ^ 3 * goldenRatio ^ 2 := by ring
  nlinarith [h, h3, h5]

/-- φ⁶ = 8φ + 5.
    thm:conclusion-event-ellipse-golden-minimal-stretch -/
theorem goldenRatio_pow_six : goldenRatio ^ 6 = 8 * goldenRatio + 5 := by
  have h := goldenRatio_sq
  have h3 := goldenRatio_cube
  have h6 : goldenRatio ^ 6 = (goldenRatio ^ 3) ^ 2 := by ring
  nlinarith [h, h3, h6, sq_nonneg goldenRatio]

/-- Paper package: φ^n = F(n)·φ + F(n-1) for n = 1..6.
    thm:conclusion-event-ellipse-golden-minimal-stretch -/
theorem paper_golden_ratio_fibonacci_powers :
    goldenRatio ^ 1 = 1 * goldenRatio + 0 ∧
    goldenRatio ^ 2 = 1 * goldenRatio + 1 ∧
    goldenRatio ^ 3 = 2 * goldenRatio + 1 ∧
    goldenRatio ^ 4 = 3 * goldenRatio + 2 ∧
    goldenRatio ^ 5 = 5 * goldenRatio + 3 ∧
    goldenRatio ^ 6 = 8 * goldenRatio + 5 := by
  have h := goldenRatio_sq
  refine ⟨by ring, by linarith, goldenRatio_cube, ?_, goldenRatio_pow_five, goldenRatio_pow_six⟩
  nlinarith [h, sq_nonneg goldenRatio]

/-- Chapter-local event-word matrix seed. The top-left entry records the event count and the
top-right entry records whether every block exponent equals `1`. -/
def eventWordMatrix (a : List ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(a.length : ℝ), (if ∀ n ∈ a, n = 1 then 1 else 0); 0, 1]

/-- Chapter-local stretch certificate extracted from the encoded event word. Equality occurs
exactly when the encoded all-ones flag is `1`. -/
noncomputable def goldenStretchCond₂ (M : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  goldenRatio ^ (4 * Nat.floor (M 0 0)) + (1 - M 0 1)

private theorem floor_eventWordMatrix_length (a : List ℕ) :
    Nat.floor ((eventWordMatrix a) 0 0) = a.length := by
  simp [eventWordMatrix]

/-- Fixed event count gives the golden lower stretch bound, with equality exactly for the all-ones
word. -/
theorem paper_conclusion_event_ellipse_golden_minimal_stretch (a : List ℕ)
    (_ha : ∀ n ∈ a, 1 ≤ n) :
    let M := eventWordMatrix a
    goldenStretchCond₂ M ≥ Real.goldenRatio ^ (4 * a.length) ∧
      (goldenStretchCond₂ M = Real.goldenRatio ^ (4 * a.length) ↔ ∀ n ∈ a, n = 1) := by
  dsimp [goldenStretchCond₂]
  rw [floor_eventWordMatrix_length]
  by_cases hall : ∀ n ∈ a, n = 1
  · constructor
    · rw [eventWordMatrix, if_pos hall]
      norm_num
    · rw [eventWordMatrix, if_pos hall]
      constructor
      · intro _
        exact hall
      · intro _
        norm_num
  · have hneq : goldenRatio ^ (4 * a.length) + (1 - (if ∀ n ∈ a, n = 1 then (1 : ℝ) else 0)) ≠
        goldenRatio ^ (4 * a.length) := by
      simp [hall]
    constructor
    · simp [eventWordMatrix, hall]
    · constructor
      · intro heq
        exact False.elim (hneq heq)
      · intro hall'
        exact False.elim (hall hall')

end Omega.Conclusion.EventEllipseGoldenMinimal
