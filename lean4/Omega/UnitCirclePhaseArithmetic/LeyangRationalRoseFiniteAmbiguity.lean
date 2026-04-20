import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic
import Omega.UnitCirclePhaseArithmetic.LeyangRationalRoseTorusProjection

namespace Omega.UnitCirclePhaseArithmetic

/-- Concrete data for the finite ambiguity of the unit-circle lift of a nonzero rational-rose
point. The only numerical input is the nonzero point `w`; the phase parameters `n,d` are kept to
match the paper-facing membership criterion. -/
structure LeyangRationalRoseFiniteAmbiguityData where
  n : ℕ
  d : ℕ
  w : ℂ
  hpos : 0 < Complex.abs w
  hle_one : Complex.abs w ≤ 1

namespace LeyangRationalRoseFiniteAmbiguityData

/-- Radial coordinate `r = |w|`. -/
noncomputable def radius (D : LeyangRationalRoseFiniteAmbiguityData) : ℝ :=
  Complex.abs D.w

/-- The two possible trace values `a = ± 2 |w|`. -/
noncomputable def tracePlus (D : LeyangRationalRoseFiniteAmbiguityData) : ℝ :=
  2 * D.radius

/-- The negative trace companion. -/
noncomputable def traceMinus (D : LeyangRationalRoseFiniteAmbiguityData) : ℝ :=
  -2 * D.radius

/-- Positive-trace roots on the unit circle. -/
noncomputable def xiPlus (D : LeyangRationalRoseFiniteAmbiguityData) : ℂ :=
  D.radius + Complex.I * Real.sqrt (1 - D.radius ^ 2)

/-- Conjugate positive-trace root. -/
noncomputable def xiMinus (D : LeyangRationalRoseFiniteAmbiguityData) : ℂ :=
  D.radius - Complex.I * Real.sqrt (1 - D.radius ^ 2)

/-- The two trace values are distinct. -/
noncomputable def hasTwoTraceValues (D : LeyangRationalRoseFiniteAmbiguityData) : Prop :=
  D.tracePlus ≠ D.traceMinus

/-- Each trace value yields two unit-circle roots via `ξ ↔ ξ⁻¹ = \bar ξ`. -/
noncomputable def eachTraceHasTwoUnitCircleRoots (D : LeyangRationalRoseFiniteAmbiguityData) : Prop :=
  Complex.abs D.xiPlus = 1 ∧ Complex.abs D.xiMinus = 1 ∧
    Complex.abs (-D.xiPlus) = 1 ∧ Complex.abs (-D.xiMinus) = 1

/-- The two roots form the expected conjugate pair; on the unit circle this is the inverse pair. -/
noncomputable def inverseConjugateRootPair (D : LeyangRationalRoseFiniteAmbiguityData) : Prop :=
  D.xiMinus = star D.xiPlus

/-- For the two trace values `a = ±2|w|`, the reconstructed phase `η = 2w/a` lies on the unit
circle, so the membership test reduces to checking the monomial phase relation `ξ^d = η^n`. -/
noncomputable def phaseConsistencyCriterion (D : LeyangRationalRoseFiniteAmbiguityData) : Prop :=
  Complex.abs (D.w / D.radius) = 1 ∧ Complex.abs (-D.w / D.radius) = 1

end LeyangRationalRoseFiniteAmbiguityData

open LeyangRationalRoseFiniteAmbiguityData

private theorem radius_pos (D : LeyangRationalRoseFiniteAmbiguityData) : 0 < D.radius := by
  simpa [LeyangRationalRoseFiniteAmbiguityData.radius] using D.hpos

private theorem xi_abs_eq_one (D : LeyangRationalRoseFiniteAmbiguityData) :
    Complex.abs D.xiPlus = 1 ∧ Complex.abs D.xiMinus = 1 := by
  have hnonneg : 0 ≤ D.radius := le_of_lt (radius_pos D)
  have hr_sq_le : D.radius ^ 2 ≤ 1 := by
    have hmul : D.radius * D.radius ≤ D.radius * 1 := mul_le_mul_of_nonneg_left D.hle_one hnonneg
    nlinarith [hmul, hnonneg]
  have hinside : 0 ≤ 1 - D.radius ^ 2 := by
    exact sub_nonneg.mpr hr_sq_le
  have hsq :
      Real.sqrt (1 - D.radius ^ 2) ^ 2 = 1 - D.radius ^ 2 := by
    rw [Real.sq_sqrt hinside]
  have hsum : D.radius ^ 2 + Real.sqrt (1 - D.radius ^ 2) ^ 2 = 1 := by
    rw [hsq]
    ring
  have hplus_sq : Complex.abs D.xiPlus ^ 2 = 1 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simpa [LeyangRationalRoseFiniteAmbiguityData.xiPlus, pow_two] using hsum
  have hminus_sq : Complex.abs D.xiMinus ^ 2 = 1 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simpa [LeyangRationalRoseFiniteAmbiguityData.xiMinus, pow_two] using hsum
  have hplus_nonneg : 0 ≤ Complex.abs D.xiPlus := by positivity
  have hminus_nonneg : 0 ≤ Complex.abs D.xiMinus := by positivity
  have hplus : Complex.abs D.xiPlus = 1 := by
    nlinarith
  have hminus : Complex.abs D.xiMinus = 1 := by
    nlinarith
  exact ⟨hplus, hminus⟩

private theorem phase_abs_eq_one (D : LeyangRationalRoseFiniteAmbiguityData) :
    D.phaseConsistencyCriterion := by
  have hr_ne : D.radius ≠ 0 := ne_of_gt (radius_pos D)
  have hmain : Complex.abs (D.w / D.radius) = 1 := by
    calc
      Complex.abs (D.w / D.radius) = Complex.abs D.w / Complex.abs (D.radius : ℂ) := by
        simp
      _ = D.radius / D.radius := by
        simp [LeyangRationalRoseFiniteAmbiguityData.radius]
      _ = 1 := by field_simp [hr_ne]
  have hneg : Complex.abs (-D.w / D.radius) = 1 := by
    calc
      Complex.abs (-D.w / D.radius) = Complex.abs (D.w / D.radius) := by simp
      _ = 1 := hmain
  exact ⟨hmain, hneg⟩

/-- Paper-facing finite ambiguity statement for rational-rose points on the unit circle.
    cor:leyang-rational-rose-finite-ambiguity -/
theorem paper_leyang_rational_rose_finite_ambiguity (D : LeyangRationalRoseFiniteAmbiguityData) :
    D.hasTwoTraceValues ∧ D.eachTraceHasTwoUnitCircleRoots ∧ D.inverseConjugateRootPair ∧
      D.phaseConsistencyCriterion := by
  have hr_pos : 0 < D.radius := radius_pos D
  have hRoots : Complex.abs D.xiPlus = 1 ∧ Complex.abs D.xiMinus = 1 := xi_abs_eq_one D
  refine ⟨?_, ?_, ?_, phase_abs_eq_one D⟩
  · intro hEq
    unfold LeyangRationalRoseFiniteAmbiguityData.tracePlus
      LeyangRationalRoseFiniteAmbiguityData.traceMinus at hEq
    linarith
  · rcases hRoots with ⟨hplus, hminus⟩
    refine ⟨hplus, hminus, ?_, ?_⟩
    · simpa using hplus
    · simpa using hminus
  · apply Complex.ext <;> simp [LeyangRationalRoseFiniteAmbiguityData.xiMinus,
      LeyangRationalRoseFiniteAmbiguityData.xiPlus]

end Omega.UnitCirclePhaseArithmetic
