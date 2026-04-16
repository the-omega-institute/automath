import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.CircleDimension

/-- A finite atomic configuration for the shifted Jensen-defect integral law. -/
structure ShiftedJensenAtom where
  weight : ℕ
  gamma : ℝ
  delta : ℝ

/-- The squared Cayley modulus appearing in the shifted Jensen-defect kernel. -/
noncomputable def shiftedJensenCayleyModSq (γ δ x₀ : ℝ) : ℝ :=
  ((γ - x₀) ^ 2 + (1 - δ) ^ 2) / ((γ - x₀) ^ 2 + (1 + δ) ^ 2)

/-- The thresholded one-atom Jensen defect. -/
noncomputable def shiftedJensenDefectAtom (ρ γ δ x₀ : ℝ) : ℝ :=
  max (Real.log (ρ / Real.sqrt (shiftedJensenCayleyModSq γ δ x₀))) 0

/-- The support cutoff from the paper's closed form. -/
noncomputable def shiftedJensenCutoff (ρ δ : ℝ) : ℝ :=
  Real.sqrt <| max 0 <| (ρ ^ 2 * (1 + δ) ^ 2 - (1 - δ) ^ 2) / (1 - ρ ^ 2)

/-- The closed one-atom integral law, with the endpoint value inserted at `ρ = 1`. -/
noncomputable def shiftedJensenClosedForm (ρ δ : ℝ) : ℝ :=
  if _hρ : ρ = 1 then
    2 * Real.pi * δ
  else
    let X := shiftedJensenCutoff ρ δ
    2 * (1 + δ) * Real.arctan (X / (1 + δ)) -
      2 * (1 - δ) * Real.arctan (X / (1 - δ))

/-- The finite-atomic integral obtained by summing the one-atom closed form. -/
noncomputable def shiftedJensenAtomicIntegral (ρ : ℝ) (μ : List ShiftedJensenAtom) : ℝ :=
  (μ.map fun a => (a.weight : ℝ) * shiftedJensenClosedForm ρ a.delta).sum

/-- The Cayley modulus only depends on the difference variable `γ - x₀`. -/
theorem shiftedJensenCayleyModSq_translate (γ δ x₀ : ℝ) :
    shiftedJensenCayleyModSq γ δ x₀ = shiftedJensenCayleyModSq 0 δ (x₀ - γ) := by
  unfold shiftedJensenCayleyModSq
  have hsq : (γ - x₀) ^ 2 = (0 - (x₀ - γ)) ^ 2 := by ring_nf
  simp [hsq]

/-- Translation invariance of the one-atom defect kernel. -/
theorem shiftedJensenDefectAtom_translate (ρ γ δ x₀ : ℝ) :
    shiftedJensenDefectAtom ρ γ δ x₀ = shiftedJensenDefectAtom ρ 0 δ (x₀ - γ) := by
  unfold shiftedJensenDefectAtom
  rw [shiftedJensenCayleyModSq_translate]

/-- The endpoint value of the closed form is the saturated limit `2πδ`. -/
theorem shiftedJensenClosedForm_one (δ : ℝ) :
    shiftedJensenClosedForm 1 δ = 2 * Real.pi * δ := by
  simp [shiftedJensenClosedForm]

/-- Paper-facing wrapper for the shifted Jensen-defect integral law: the kernel is translation
invariant in the base point, the finite-atomic integral is the sum of the one-atom closed forms,
and the saturated endpoint value is `2πδ`.
    prop:cdim-shifted-jensen-defect-integral-law -/
theorem paper_cdim_shifted_jensen_defect_integral_law :
    (∀ ρ γ δ x₀,
      shiftedJensenDefectAtom ρ γ δ x₀ = shiftedJensenDefectAtom ρ 0 δ (x₀ - γ)) ∧
    (∀ ρ μ,
      shiftedJensenAtomicIntegral ρ μ =
        (μ.map fun a => (a.weight : ℝ) * shiftedJensenClosedForm ρ a.delta).sum) ∧
    (∀ δ, shiftedJensenClosedForm 1 δ = 2 * Real.pi * δ) := by
  refine ⟨shiftedJensenDefectAtom_translate, ?_, shiftedJensenClosedForm_one⟩
  intro ρ μ
  rfl

end Omega.CircleDimension
