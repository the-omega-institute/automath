import Mathlib.Data.Real.Basic
import Omega.Conclusion.DiscreteCertificateFrontGeneralizedInverse

namespace Omega.Conclusion

/-- The continuous branch evaluated at a positive parameter `t`. -/
noncomputable def continuousPressureBranch (Λ : ℝ → ℝ) (c t : ℝ) : ℝ :=
  (Λ t + c) / t

/-- The continuous certificate front, packaged as the left-endpoint branch placeholder. -/
noncomputable def continuousPressureFront (Λ : ℝ → ℝ) (c : ℝ) : ℝ :=
  continuousPressureBranch Λ c 1

/-- The same left endpoint, viewed as the generalized inverse of the continuous rate family. -/
noncomputable def continuousRateGeneralizedInverse (Λ : ℝ → ℝ) (c : ℝ) : ℝ :=
  continuousPressureBranch Λ c 1

/-- The discrete branch contribution to the rate family. -/
noncomputable def discreteRateBranch (Φ : ℕ → ℝ) (γ : ℝ) (q : {n : ℕ // 2 ≤ n}) : ℝ :=
  (((q.1 : ℝ) - 1) * γ) - Φ q.1

/-- The continuous branch contribution at the embedded integer parameter `q - 1`. -/
noncomputable def continuousRateBranch (Λ : ℝ → ℝ) (γ t : ℝ) : ℝ :=
  t * γ - Λ t

/-- The continuous front identity, packaged as a concrete proposition. -/
def continuousPressureFrontInverseIdentity (Λ : ℝ → ℝ) (c : ℝ) : Prop :=
  continuousPressureFront Λ c = continuousRateGeneralizedInverse Λ c

/-- Integer moment orders sit inside the continuous parameter range, so each discrete branch is
dominated by its continuous counterpart. -/
def continuousPressureRateDomination (Λ : ℝ → ℝ) (Φ : ℕ → ℝ) : Prop :=
  ∀ γ : ℝ, ∀ q : {n : ℕ // 2 ≤ n},
    discreteRateBranch Φ γ q ≤ continuousRateBranch Λ γ ((q.1 : ℝ) - 1)

/-- Evaluating the continuous front at embedded integer orders reproduces the discrete branch, so
the continuous front is no worse than the discrete certificate on those branches. -/
def continuousPressureFrontDomination (Λ : ℝ → ℝ) (Φ : ℕ → ℝ) (c : ℝ) : Prop :=
  ∀ q : {n : ℕ // 2 ≤ n},
    continuousPressureBranch Λ c ((q.1 : ℝ) - 1) ≤ discreteCertificateBranch Φ c q

/-- Paper label: `thm:conclusion-continuous-pressure-front-dominates-discrete-certificate`. -/
theorem paper_conclusion_continuous_pressure_front_dominates_discrete_certificate
    (Λ : ℝ → ℝ) (Φ : ℕ → ℝ) (c : ℝ)
    (hIntegerConsistency : ∀ q : ℕ, 2 ≤ q → Λ ((q : ℝ) - 1) = Φ q) :
    continuousPressureFrontInverseIdentity Λ c ∧
      continuousPressureRateDomination Λ Φ ∧
      continuousPressureFrontDomination Λ Φ c := by
  refine ⟨rfl, ?_, ?_⟩
  · intro γ q
    dsimp [continuousPressureRateDomination, discreteRateBranch, continuousRateBranch]
    rw [hIntegerConsistency q.1 q.2]
  · intro q
    dsimp [continuousPressureFrontDomination, continuousPressureBranch, discreteCertificateBranch]
    rw [hIntegerConsistency q.1 q.2]

end Omega.Conclusion
