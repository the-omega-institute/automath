import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

noncomputable section

/-- Audited sextic equation for the weighted Perron branch. -/
def weightedCompletionSextic (l u : ℝ) : ℝ :=
  l ^ 6 - (1 + u) * l ^ 5 - 5 * u * l ^ 4 + 3 * u * (1 + u) * l ^ 3 -
    u * (u ^ 2 - 3 * u + 1) * l ^ 2 + u * (u ^ 3 - 3 * u ^ 2 - 3 * u + 1) * l +
    u ^ 2 * (u ^ 2 + u + 1)

/-- Laurent form obtained from `weightedCompletionSextic (r * y) (r^2) / r^6`. -/
def weightedCompletionLaurent (r y : ℝ) : ℝ :=
  y ^ 6 - (r + r⁻¹) * y ^ 5 - 5 * y ^ 4 + 3 * (r + r⁻¹) * y ^ 3 -
    (r ^ 2 - 3 + (r⁻¹) ^ 2) * y ^ 2 + (r ^ 3 - 3 * r - 3 * r⁻¹ + (r⁻¹) ^ 3) * y +
    (r ^ 2 + 1 + (r⁻¹) ^ 2)

/-- The descended polynomial in the inversion-invariant coordinate `s = r + r⁻¹`. -/
def weightedCompletionQ (s y : ℝ) : ℝ :=
  y ^ 6 - s * y ^ 5 - 5 * y ^ 4 + 3 * s * y ^ 3 + (5 - s ^ 2) * y ^ 2 +
    (s ^ 3 - 6 * s) * y + (s ^ 2 - 1)

lemma weightedCompletionSextic_substitution (r y : ℝ) (hr : r ≠ 0) :
    weightedCompletionSextic (r * y) (r ^ 2) = r ^ 6 * weightedCompletionLaurent r y := by
  unfold weightedCompletionSextic weightedCompletionLaurent
  field_simp [hr]
  ring_nf

lemma weightedCompletionLaurent_eq_Q (r y : ℝ) (hr : r ≠ 0) :
    weightedCompletionLaurent r y = weightedCompletionQ (r + r⁻¹) y := by
  unfold weightedCompletionLaurent weightedCompletionQ
  field_simp [hr]
  ring_nf

lemma weightedCompletionLaurent_invariant (r y : ℝ) (hr : r ≠ 0) :
    weightedCompletionLaurent (r⁻¹) y = weightedCompletionLaurent r y := by
  rw [weightedCompletionLaurent_eq_Q (r := r⁻¹) (y := y) (inv_ne_zero hr)]
  rw [weightedCompletionLaurent_eq_Q (r := r) (y := y) hr]
  simp [add_comm]

lemma weightedCompletion_eq_zero_iff (r y : ℝ) (hr : r ≠ 0) :
    weightedCompletionSextic (r * y) (r ^ 2) = 0 ↔ weightedCompletionQ (r + r⁻¹) y = 0 := by
  rw [weightedCompletionSextic_substitution r y hr, weightedCompletionLaurent_eq_Q r y hr]
  have hr6 : r ^ 6 ≠ 0 := pow_ne_zero 6 hr
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_left hr6
  · intro h
    rw [h]
    ring

/-- Paper label: `prop:weighted-completion-Q`.
After the completion substitution `u = r^2`, `λ = r y`, the sextic reduces to the invariant
polynomial `weightedCompletionQ (r + r⁻¹) y`, and under `r = exp (θ/2)` the pressure identity is
the logarithmic factorization `log (r y) = θ/2 + log y`. -/
theorem paper_weighted_completion_q (r y θ : ℝ) (hr : r ≠ 0) (hy : 0 < y)
    (hθ : r = Real.exp (θ / 2)) :
    weightedCompletionLaurent (r⁻¹) y = weightedCompletionLaurent r y ∧
      (weightedCompletionSextic (r * y) (r ^ 2) = 0 ↔ weightedCompletionQ (r + r⁻¹) y = 0) ∧
      (weightedCompletionSextic (r * y) (r ^ 2) = 0 ↔
        weightedCompletionQ (2 * Real.cosh (θ / 2)) y = 0) ∧
      Real.log (r * y) = θ / 2 + Real.log y := by
  have hs : r + r⁻¹ = 2 * Real.cosh (θ / 2) := by
    rw [hθ, Real.cosh_eq]
    rw [Real.exp_neg]
    ring
  have hr_pos : 0 < r := by
    rw [hθ]
    exact Real.exp_pos _
  refine ⟨weightedCompletionLaurent_invariant r y hr, weightedCompletion_eq_zero_iff r y hr, ?_, ?_⟩
  · rw [weightedCompletion_eq_zero_iff r y hr, hs]
  · rw [hθ, Real.log_mul (by positivity) (ne_of_gt hy), Real.log_exp]

end

end Omega.SyncKernelWeighted
