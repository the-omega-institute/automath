import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

noncomputable section

/-- Linearized activated branch denominator at the critical real input `u = 1`. -/
def realInput40ActivatedDenominator (u : ℝ) : ℝ :=
  u - 1

/-- Analytic numerator with prescribed value `H₁` at `u = 1`. -/
def realInput40ActivatedNumerator (H₁ slope u : ℝ) : ℝ :=
  H₁ + slope * (u - 1)

/-- The corresponding activated branch observable. -/
def realInput40ActivatedObservable (H₁ slope u : ℝ) : ℝ :=
  realInput40ActivatedNumerator H₁ slope u / realInput40ActivatedDenominator u

/-- The activated branch has a universal simple pole at `u = 1`: the singular part is exactly
`H₁ / (u - 1)` and the residue equals the nonzero analytic numerator value `H₁`.
`thm:killo-real-input-40-activated-branch-simple-pole` -/
theorem paper_killo_real_input_40_activated_branch_simple_pole
    (H₁ slope u : ℝ) (hH₁ : H₁ ≠ 0) (hu : u ≠ 1) :
    (1 / realInput40ActivatedDenominator u = 1 / (u - 1)) ∧
      (realInput40ActivatedObservable H₁ slope u = H₁ / (u - 1) + slope) ∧
      ((u - 1) * realInput40ActivatedObservable H₁ slope u =
        realInput40ActivatedNumerator H₁ slope u) ∧
      (realInput40ActivatedNumerator H₁ slope 1 = H₁) ∧
      (realInput40ActivatedNumerator H₁ slope 1 ≠ 0) := by
  have hud : u - 1 ≠ 0 := sub_ne_zero.mpr hu
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · unfold realInput40ActivatedObservable realInput40ActivatedNumerator realInput40ActivatedDenominator
    field_simp [hud]
  · unfold realInput40ActivatedObservable realInput40ActivatedNumerator realInput40ActivatedDenominator
    field_simp [hud]
  · simp [realInput40ActivatedNumerator]
  · simpa [realInput40ActivatedNumerator] using hH₁
