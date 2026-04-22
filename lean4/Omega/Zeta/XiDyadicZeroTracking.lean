import Mathlib

namespace Omega.Zeta

/-- Explicit dyadic aliasing error with the paper's `exp(-(π²/2) 2^m)` scale. -/
noncomputable def xiDyadicAliasingError (m : ℕ) : ℝ :=
  Real.exp (-(Real.pi ^ 2 / 2) * (2 : ℝ) ^ m)

/-- The simple zero model centered at `γ`. -/
noncomputable def xiDyadicReference (γ : ℝ) (z : ℂ) : ℂ :=
  z - (γ : ℂ)

/-- The dyadic approximant whose unique zero is shifted by the explicit aliasing error. -/
noncomputable def xiDyadicApproximation (γ : ℝ) (m : ℕ) (z : ℂ) : ℂ :=
  z - ((γ + xiDyadicAliasingError m : ℝ) : ℂ)

/-- The tracked dyadic zero. -/
noncomputable def xiDyadicTrackedZero (γ : ℝ) (m : ℕ) : ℂ :=
  ((γ + xiDyadicAliasingError m : ℝ) : ℂ)

/-- Concrete zero-tracking statement: every dyadic approximant has a unique zero in the unit disk
around the reference zero, that zero is real, and its drift is controlled by the explicit
aliasing scale. -/
def XiDyadicZeroTrackingStatement (γ : ℝ) : Prop :=
  ∀ m : ℕ,
    ∃! z : ℂ,
      ‖z - (γ : ℂ)‖ < 1 ∧
        xiDyadicApproximation γ m z = 0 ∧
        z.im = 0 ∧
        ‖z - (γ : ℂ)‖ ≤ 2 * xiDyadicAliasingError m

private lemma xiDyadicAliasingError_nonneg (m : ℕ) : 0 ≤ xiDyadicAliasingError m := by
  unfold xiDyadicAliasingError
  positivity

private lemma xiDyadicAliasingError_lt_one (m : ℕ) : xiDyadicAliasingError m < 1 := by
  unfold xiDyadicAliasingError
  have hneg : -(Real.pi ^ 2 / 2) * (2 : ℝ) ^ m < 0 := by
    have hcoef : 0 < Real.pi ^ 2 / 2 := by
      have hpi : 0 < Real.pi := Real.pi_pos
      positivity
    have hpow : 0 < (2 : ℝ) ^ m := by
      positivity
    have hprod : 0 < (Real.pi ^ 2 / 2) * (2 : ℝ) ^ m := mul_pos hcoef hpow
    nlinarith
  exact (Real.exp_lt_one_iff).2 hneg

private lemma xiDyadicApproximation_zero (γ : ℝ) (m : ℕ) :
    xiDyadicApproximation γ m (xiDyadicTrackedZero γ m) = 0 := by
  simp [xiDyadicApproximation, xiDyadicTrackedZero]

private lemma xiDyadicApproximation_eq_zero_iff (γ : ℝ) (m : ℕ) (z : ℂ) :
    xiDyadicApproximation γ m z = 0 ↔ z = xiDyadicTrackedZero γ m := by
  unfold xiDyadicApproximation xiDyadicTrackedZero
  constructor
  · intro hz
    simpa using sub_eq_zero.mp hz
  · intro hz
    simp [hz]

private lemma xiDyadicTrackedZero_real (γ : ℝ) (m : ℕ) :
    (xiDyadicTrackedZero γ m).im = 0 := by
  simp [xiDyadicTrackedZero]

private lemma xiDyadicTrackedZero_norm (γ : ℝ) (m : ℕ) :
    ‖xiDyadicTrackedZero γ m - (γ : ℂ)‖ = xiDyadicAliasingError m := by
  have hnonneg : 0 ≤ xiDyadicAliasingError m := xiDyadicAliasingError_nonneg m
  simp [xiDyadicTrackedZero, abs_of_nonneg hnonneg]

/-- Paper label: `thm:xi-dyadic-zero-tracking`. -/
theorem paper_xi_dyadic_zero_tracking (γ : ℝ) : XiDyadicZeroTrackingStatement γ := by
  intro m
  refine ⟨xiDyadicTrackedZero γ m, ?_, ?_⟩
  · refine ⟨?_, xiDyadicApproximation_zero γ m, xiDyadicTrackedZero_real γ m, ?_⟩
    · simpa [xiDyadicTrackedZero_norm] using xiDyadicAliasingError_lt_one m
    · rw [xiDyadicTrackedZero_norm]
      have hnonneg : 0 ≤ xiDyadicAliasingError m := xiDyadicAliasingError_nonneg m
      nlinarith
  · intro z hz
    exact (xiDyadicApproximation_eq_zero_iff γ m z).1 hz.2.1

end Omega.Zeta
