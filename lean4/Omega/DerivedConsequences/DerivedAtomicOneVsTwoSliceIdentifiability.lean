import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import Omega.DerivedConsequences.DerivedAtomicTwoSliceTomography

namespace Omega.DerivedConsequences

noncomputable section

/-- Paper label: `cor:derived-atomic-one-vs-two-slice-identifiability`. A single slice equation
`c = m u^E` leaves a one-parameter ambiguity, while the existing two-slice theorem recovers the
continuous atomic parameters from any two distinct positive slices. -/
theorem paper_derived_atomic_one_vs_two_slice_identifiability :
    (∀ {u m E : ℝ}, 0 < u → ∃ m' E' : ℝ, (m', E') ≠ (m, E) ∧
      derived_atomic_two_slice_tomography_slice_coeff u m' E' =
        derived_atomic_two_slice_tomography_slice_coeff u m E) ∧
      derived_atomic_two_slice_tomography_statement := by
  refine ⟨?_, paper_derived_atomic_two_slice_tomography⟩
  intro u m E hu
  refine ⟨m * u ^ (-1 : ℝ), E + 1, ?_, ?_⟩
  · intro hpair
    have hE : E + 1 = E := by
      simpa using congrArg Prod.snd hpair
    linarith
  · calc
      derived_atomic_two_slice_tomography_slice_coeff u (m * u ^ (-1 : ℝ)) (E + 1)
          = (m * u ^ (-1 : ℝ)) * u ^ (E + 1) := by
              simp [derived_atomic_two_slice_tomography_slice_coeff]
      _ = (m * u⁻¹) * (u ^ E * u) := by
            rw [Real.rpow_neg_one, Real.rpow_add_one hu.ne' E]
      _ = m * (u⁻¹ * (u ^ E * u)) := by ring
      _ = m * (u ^ E * (u⁻¹ * u)) := by ring
      _ = m * (u ^ E * 1) := by rw [inv_mul_cancel₀ hu.ne']
      _ = derived_atomic_two_slice_tomography_slice_coeff u m E := by
            simp [derived_atomic_two_slice_tomography_slice_coeff]

end

end Omega.DerivedConsequences
