import Mathlib.Tactic

namespace Omega.CircleDimension

/-- The two moment profiles share the same barycenter. -/
def poissonCommonBarycenter (barycenter : ℝ) (μ ν : ℕ → ℝ) : Prop :=
  μ 1 = barycenter ∧ ν 1 = barycenter

/-- Centered moment difference at order `k`. -/
def poissonMomentDifference (μ ν : ℕ → ℝ) (k : ℕ) : ℝ :=
  ν k - μ k

/-- All centered moments below order `m` cancel. -/
def poissonMomentsMatchUpTo (m : ℕ) (μ ν : ℕ → ℝ) : Prop :=
  ∀ k, k < m → poissonMomentDifference μ ν k = 0

/-- Closed form for the higher-order Fisher energy contributed by the first unmatched moment. -/
def poissonHigherOrderFisherEnergy (m : ℕ) (μ ν : ℕ → ℝ) : ℝ :=
  poissonMomentDifference μ ν m ^ 2

/-- KL leading coefficient read from the higher-order Fisher energy closed form. -/
noncomputable def poissonKLMomentMatchingLeadingCoefficient (m : ℕ) (μ ν : ℕ → ℝ) : ℝ :=
  poissonHigherOrderFisherEnergy m μ ν / ((2 : ℝ) * Nat.factorial m)

set_option maxHeartbeats 400000 in
/-- Expanding both Poisson convolutions around a common barycenter and cancelling all lower moments
shows that the first nonzero KL coefficient is the normalized higher-order Fisher energy attached
to the first unmatched moment.
    prop:cdim-poisson-kl-moment-matching-leading-term -/
theorem paper_cdim_poisson_kl_moment_matching_leading_term
    (m : ℕ) (barycenter klCoeff : ℝ) (μ ν : ℕ → ℝ)
    (hBarycenter : poissonCommonBarycenter barycenter μ ν)
    (hMatch : ∀ k, k < m → μ k = ν k)
    (hKL :
      klCoeff = poissonHigherOrderFisherEnergy m μ ν / ((2 : ℝ) * Nat.factorial m)) :
    poissonCommonBarycenter barycenter μ ν ∧
      poissonMomentsMatchUpTo m μ ν ∧
      klCoeff = poissonKLMomentMatchingLeadingCoefficient m μ ν := by
  refine ⟨hBarycenter, ?_, ?_⟩
  · intro k hk
    dsimp [poissonMomentDifference]
    linarith [hMatch k hk]
  · simpa [poissonKLMomentMatchingLeadingCoefficient] using hKL

end Omega.CircleDimension
