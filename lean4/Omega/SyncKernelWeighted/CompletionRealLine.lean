import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Omega.SyncKernelWeighted.UnitarySliceHalfPhaseLocking

namespace Omega.SyncKernelWeighted

open scoped ComplexConjugate

noncomputable section

/-- The completed coefficient on the unitary slice after dividing by the half-phase. -/
def completion_real_line_completed_coeff (d : ℂ → ℂ) (θ : ℝ) : ℂ :=
  d (unitarySlicePoint θ) / unitarySliceHalfPhase θ

/-- Paper-facing real-line completion statement for a self-dual conjugation-symmetric branch. -/
def completion_real_line_statement : Prop :=
  ∀ d : ℂ → ℂ,
    (∀ u : ℂ, d u = u * d (u⁻¹)) →
    (∀ u : ℂ, d (conj u) = conj (d u)) →
    (∀ θ : ℝ,
      conj (completion_real_line_completed_coeff d θ) =
        completion_real_line_completed_coeff d θ) ∧
      ∀ θ : ℝ, ∃ r : ℝ, completion_real_line_completed_coeff d θ = r

/-- Paper label: `cor:completion-real-line`. -/
theorem paper_completion_real_line : completion_real_line_statement := by
  intro d hSelfDual hConj
  rcases paper_kernel_unitary_slice_half_phase_locking d hSelfDual hConj with ⟨hreal, _⟩
  refine ⟨?_, ?_⟩
  · intro θ
    simpa [completion_real_line_completed_coeff] using hreal θ
  · intro θ
    have hz :
        conj (completion_real_line_completed_coeff d θ) =
          completion_real_line_completed_coeff d θ := by
      simpa [completion_real_line_completed_coeff] using hreal θ
    exact Complex.conj_eq_iff_real.mp hz

end

end Omega.SyncKernelWeighted
