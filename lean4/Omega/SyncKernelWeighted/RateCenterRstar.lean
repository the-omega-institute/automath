import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic
import Omega.SyncKernelWeighted.RateCurveCenterSliceAudit

namespace Omega.SyncKernelWeighted

/-- The audited palindromic center-slice factor `Q(u)` viewed over `ℂ`. -/
def rateCenterQComplex (u : ℂ) : ℂ :=
  16 * (u ^ 2 + 1) ^ 8

private theorem rateCenterQComplex_root_iff (u : ℂ) :
    rateCenterQComplex u = 0 ↔ u = Complex.I ∨ u = -Complex.I := by
  unfold rateCenterQComplex
  constructor
  · intro hu
    have hpow : (u ^ 2 + 1) ^ 8 = 0 := by
      have h16 : (16 : ℂ) ≠ 0 := by norm_num
      exact (mul_eq_zero.mp hu).resolve_left h16
    have hquad : u ^ 2 + 1 = 0 := eq_zero_of_pow_eq_zero hpow
    have hfactor : (u - Complex.I) * (u + Complex.I) = 0 := by
      calc
        (u - Complex.I) * (u + Complex.I) = u ^ 2 - Complex.I ^ 2 := by ring
        _ = u ^ 2 + 1 := by simp
        _ = 0 := hquad
    rcases mul_eq_zero.mp hfactor with huI | huNegI
    · exact Or.inl (sub_eq_zero.mp huI)
    · exact Or.inr ((eq_neg_iff_add_eq_zero).2 huNegI)
  · rintro (rfl | rfl) <;> simp

private theorem norm_sq_I_sub_one : ‖(Complex.I : ℂ) - 1‖ ^ 2 = 2 := by
  calc
    ‖(Complex.I : ℂ) - 1‖ ^ 2 = Complex.normSq ((Complex.I : ℂ) - 1) := by
      exact (Complex.normSq_eq_norm_sq _).symm
    _ = 2 := by
      rw [Complex.normSq_sub]
      norm_num

private theorem norm_sq_negI_sub_one : ‖(-Complex.I : ℂ) - 1‖ ^ 2 = 2 := by
  calc
    ‖(-Complex.I : ℂ) - 1‖ ^ 2 = Complex.normSq ((-Complex.I : ℂ) - 1) := by
      exact (Complex.normSq_eq_norm_sq _).symm
    _ = 2 := by
      rw [Complex.normSq_sub]
      norm_num

private theorem one_le_norm_I_sub_one : (1 : ℝ) ≤ ‖(Complex.I : ℂ) - 1‖ := by
  have hnonneg : 0 ≤ ‖(Complex.I : ℂ) - 1‖ := norm_nonneg _
  nlinarith [norm_sq_I_sub_one]

private theorem one_le_norm_negI_sub_one : (1 : ℝ) ≤ ‖(-Complex.I : ℂ) - 1‖ := by
  have hnonneg : 0 ≤ ‖(-Complex.I : ℂ) - 1‖ := norm_nonneg _
  nlinarith [norm_sq_negI_sub_one]

/-- The center-slice audit exposes a reciprocal, real-root-free palindromic polynomial whose
closest conjugate roots to the real center `u = 1` are the explicit pair `± i`; in particular,
every complex root lies at distance at least `1` from the center.
    cor:rate-center-Rstar -/
theorem paper_rate_center_rstar :
    rateCenterQReciprocalIdentity ∧
      rateCenterQNoRealRoots ∧
      rateCenterQComplex Complex.I = 0 ∧
      rateCenterQComplex (-Complex.I) = 0 ∧
      ‖(Complex.I : ℂ) - 1‖ = ‖(-Complex.I : ℂ) - 1‖ ∧
      ∀ u : ℂ, rateCenterQComplex u = 0 → (1 : ℝ) ≤ ‖u - 1‖ := by
  rcases paper_rate_center_q_reciprocal_no_real with ⟨hReciprocal, hNoRealRoots, _⟩
  refine ⟨hReciprocal, hNoRealRoots, ?_, ?_, ?_, ?_⟩
  · simp [rateCenterQComplex]
  · simp [rateCenterQComplex]
  · have hI_nonneg : 0 ≤ ‖(Complex.I : ℂ) - 1‖ := norm_nonneg _
    have hNegI_nonneg : 0 ≤ ‖(-Complex.I : ℂ) - 1‖ := norm_nonneg _
    nlinarith [norm_sq_I_sub_one, norm_sq_negI_sub_one]
  · intro u hu
    rcases (rateCenterQComplex_root_iff u).1 hu with rfl | rfl
    · exact one_le_norm_I_sub_one
    · exact one_le_norm_negI_sub_one

end Omega.SyncKernelWeighted
