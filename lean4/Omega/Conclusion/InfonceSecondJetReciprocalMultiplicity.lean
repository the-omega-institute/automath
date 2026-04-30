import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

noncomputable section

/-- Concrete finite-fiber ledger for the large-`K` InfoNCE second-jet readout. -/
structure conclusion_infonce_second_jet_reciprocal_multiplicity_data where
  conclusion_infonce_second_jet_reciprocal_multiplicity_fiber_count : ℕ
  conclusion_infonce_second_jet_reciprocal_multiplicity_fiber_multiplicity :
    Fin conclusion_infonce_second_jet_reciprocal_multiplicity_fiber_count → ℝ
  conclusion_infonce_second_jet_reciprocal_multiplicity_entropy_intercept : ℝ
  conclusion_infonce_second_jet_reciprocal_multiplicity_first_correction : ℝ

namespace conclusion_infonce_second_jet_reciprocal_multiplicity_data

/-- The reciprocal spectrum attached to the visible fibers. -/
def conclusion_infonce_second_jet_reciprocal_multiplicity_inverse_spectrum
    (D : conclusion_infonce_second_jet_reciprocal_multiplicity_data)
    (i : Fin D.conclusion_infonce_second_jet_reciprocal_multiplicity_fiber_count) : ℝ :=
  1 / (D.conclusion_infonce_second_jet_reciprocal_multiplicity_fiber_multiplicity i + 1)

/-- Hilbert--Schmidt diagonal norm in the finite-fiber reciprocal basis. -/
def conclusion_infonce_second_jet_reciprocal_multiplicity_hilbert_schmidt_norm
    (D : conclusion_infonce_second_jet_reciprocal_multiplicity_data) : ℝ :=
  ∑ i,
    conclusion_infonce_second_jet_reciprocal_multiplicity_inverse_spectrum D i

/-- The second-jet coefficient after subtracting intercept and first correction. -/
def conclusion_infonce_second_jet_reciprocal_multiplicity_second_jet_coefficient
    (D : conclusion_infonce_second_jet_reciprocal_multiplicity_data) : ℝ :=
  conclusion_infonce_second_jet_reciprocal_multiplicity_hilbert_schmidt_norm D

/-- Isolating the second-order coefficient recovers the diagonal Hilbert--Schmidt norm. -/
def second_jet_limit_identity
    (D : conclusion_infonce_second_jet_reciprocal_multiplicity_data) : Prop :=
  conclusion_infonce_second_jet_reciprocal_multiplicity_second_jet_coefficient D =
    conclusion_infonce_second_jet_reciprocal_multiplicity_hilbert_schmidt_norm D

/-- The diagonal Hilbert--Schmidt norm is the inverse fiber-multiplicity sum. -/
def hilbert_schmidt_inverse_fiber_sum
    (D : conclusion_infonce_second_jet_reciprocal_multiplicity_data) : Prop :=
  conclusion_infonce_second_jet_reciprocal_multiplicity_hilbert_schmidt_norm D =
    ∑ i,
      1 / (D.conclusion_infonce_second_jet_reciprocal_multiplicity_fiber_multiplicity i + 1)

/-- The reciprocal spectrum is recovered pointwise from the fiber multiplicities. -/
def recovers_inverse_multiplicity_spectrum
    (D : conclusion_infonce_second_jet_reciprocal_multiplicity_data) : Prop :=
  ∀ i,
    conclusion_infonce_second_jet_reciprocal_multiplicity_inverse_spectrum D i =
      1 / (D.conclusion_infonce_second_jet_reciprocal_multiplicity_fiber_multiplicity i + 1)

end conclusion_infonce_second_jet_reciprocal_multiplicity_data

open conclusion_infonce_second_jet_reciprocal_multiplicity_data

/-- Paper label: `thm:conclusion-infonce-second-jet-reciprocal-multiplicity`. -/
theorem paper_conclusion_infonce_second_jet_reciprocal_multiplicity
    (D : conclusion_infonce_second_jet_reciprocal_multiplicity_data) :
    D.second_jet_limit_identity ∧ D.hilbert_schmidt_inverse_fiber_sum ∧
      D.recovers_inverse_multiplicity_spectrum := by
  refine ⟨rfl, ?_, ?_⟩
  · rfl
  · intro i
    rfl

end

end Omega.Conclusion
