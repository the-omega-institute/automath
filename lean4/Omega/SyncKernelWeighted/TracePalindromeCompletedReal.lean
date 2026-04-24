import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic
import Omega.Core.OdometerJoukowsky
import Omega.SyncKernelWeighted.TracePalindrome

namespace Omega.SyncKernelWeighted

noncomputable section

/-- Concrete data for the completed trace-palindrome amplitude. -/
structure TracePalindromeCompletedRealData where
  n : ℕ

namespace TracePalindromeCompletedRealData

/-- The half-phase-normalized completed amplitude on the unit circle. For the concrete family
`a_n(u) = (u + 1)^n`, this is `J(e^{i θ / 2})^n`. -/
def completedAmplitude (D : TracePalindromeCompletedRealData) (θ : ℝ) : ℂ :=
  (Omega.POM.joukowsky (Complex.exp ((((θ / 2 : ℝ) : ℂ) * Complex.I)))) ^ D.n

/-- The completed amplitude takes real values. -/
def completedAmplitudeReal (D : TracePalindromeCompletedRealData) : Prop :=
  ∀ θ : ℝ, ∃ r : ℝ, D.completedAmplitude θ = r

/-- The completed amplitude is an even function of the phase. -/
def completedAmplitudeEven (D : TracePalindromeCompletedRealData) : Prop :=
  ∀ θ : ℝ, D.completedAmplitude (-θ) = D.completedAmplitude θ

lemma completedAmplitude_eq_cosine_power (D : TracePalindromeCompletedRealData) (θ : ℝ) :
    D.completedAmplitude θ = (2 * Real.cos (θ / 2) : ℂ) ^ D.n := by
  unfold completedAmplitude
  rw [Omega.POM.joukowsky_exp_I_mul (θ / 2)]

lemma completedAmplitudeReal_true (D : TracePalindromeCompletedRealData) :
    D.completedAmplitudeReal := by
  intro θ
  refine ⟨(2 * Real.cos (θ / 2)) ^ D.n, ?_⟩
  simpa using D.completedAmplitude_eq_cosine_power θ

lemma completedAmplitudeEven_true (D : TracePalindromeCompletedRealData) :
    D.completedAmplitudeEven := by
  intro θ
  rw [D.completedAmplitude_eq_cosine_power, D.completedAmplitude_eq_cosine_power]
  congr 1
  have hhalf : (-θ) / 2 = -(θ / 2) := by ring
  rw [hhalf, Real.cos_neg]

end TracePalindromeCompletedRealData

open TracePalindromeCompletedRealData

/-- Paper label: `cor:trace-palindrome-completed-real`. -/
theorem paper_trace_palindrome_completed_real (D : TracePalindromeCompletedRealData) :
    D.completedAmplitudeReal ∧ D.completedAmplitudeEven := by
  let _ := paper_trace_palindrome
  exact ⟨D.completedAmplitudeReal_true, D.completedAmplitudeEven_true⟩

end

end Omega.SyncKernelWeighted
