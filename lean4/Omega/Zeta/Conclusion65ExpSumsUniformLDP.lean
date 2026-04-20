import Mathlib

namespace Omega.Zeta

open scoped BigOperators

/-- Exponential sum attached to the valuation of the legal words of length `m`. -/
noncomputable def exponentialSum {α : Type*} (legalWords : ℕ → Finset α) (valuation : α → ℝ)
    (m : ℕ) (θ : ℝ) : ℂ :=
  Finset.sum (legalWords m) fun ω => Complex.exp (Complex.I * (((θ * valuation ω : ℝ) : ℂ)))

/-- The transfer-operator iterate computes the same exponential sum. -/
def TwistedTransferMatchesExponentialSum {α : Type*} (legalWords : ℕ → Finset α)
    (valuation : α → ℝ) (transferSignal : ℕ → ℝ → ℂ) : Prop :=
  ∀ m θ, exponentialSum legalWords valuation m θ = transferSignal m θ

/-- Spectral decomposition bound coming from the Perron branch of the twisted transfer operator. -/
def SpectralDecompositionBound (transferSignal : ℕ → ℝ → ℂ) (lambda : ℝ → ℝ) (C : ℝ) : Prop :=
  ∀ m θ, ‖transferSignal m θ‖ ≤ C * |lambda θ| ^ m

/-- The analytic Perron branch is represented concretely by a smooth branch with positive value
at the untwisted point. -/
def AnalyticPerronBranch (lambda : ℝ → ℝ) : Prop :=
  ContDiff ℝ ⊤ lambda ∧ 0 < lambda 0

/-- Logarithmic spectral-radius defect relative to the untwisted Perron root. -/
noncomputable def logSpectralRadiusDefect (lambda : ℝ → ℝ) (θ : ℝ) : ℝ :=
  Real.log |lambda 0| - Real.log |lambda θ|

/-- Uniform quadratic lower bound on the logarithmic spectral-radius defect away from resonance. -/
def UniformCurvatureLowerBound (lambda : ℝ → ℝ) (resonanceSet K : Set ℝ) (c : ℝ) : Prop :=
  ∀ ⦃θ : ℝ⦄, θ ∈ K → c * Metric.infDist θ resonanceSet ^ 2 ≤ logSpectralRadiusDefect lambda θ

private theorem exponentialSum_bound_of_spectral_wrapper {α : Type*}
    (legalWords : ℕ → Finset α) (valuation : α → ℝ) (transferSignal : ℕ → ℝ → ℂ)
    (lambda : ℝ → ℝ) (C : ℝ)
    (hwrapper : TwistedTransferMatchesExponentialSum legalWords valuation transferSignal)
    (hspectral : SpectralDecompositionBound transferSignal lambda C) :
    ∀ m θ, ‖exponentialSum legalWords valuation m θ‖ ≤ C * |lambda θ| ^ m := by
  intro m θ
  rw [hwrapper m θ]
  exact hspectral m θ

private theorem log_radius_abs_drop_of_uniform_curvature (lambda : ℝ → ℝ)
    (resonanceSet K : Set ℝ) (c : ℝ)
    (hcurvature : UniformCurvatureLowerBound lambda resonanceSet K c) :
    ∀ ⦃θ : ℝ⦄, θ ∈ K →
      Real.log |lambda θ| ≤ Real.log |lambda 0| - c * Metric.infDist θ resonanceSet ^ 2 := by
  intro θ hθ
  have hdrop : c * Metric.infDist θ resonanceSet ^ 2 ≤ logSpectralRadiusDefect lambda θ :=
    hcurvature hθ
  dsimp [logSpectralRadiusDefect] at hdrop ⊢
  linarith

/-- Paper-facing abstract transfer-operator wrapper for Conclusion 65: the spectral decomposition
controls the exponential sum through the Perron branch, and a uniform curvature lower bound on
the log spectral-radius defect yields quadratic decay away from resonance.
    prop:conclusion65-expsums-uniform-ldp -/
theorem paper_conclusion65_expsums_uniform_ldp {α : Type*}
    (legalWords : ℕ → Finset α) (valuation : α → ℝ) (transferSignal : ℕ → ℝ → ℂ)
    (lambda : ℝ → ℝ) (resonanceSet K : Set ℝ) (C c : ℝ)
    (hwrapper : TwistedTransferMatchesExponentialSum legalWords valuation transferSignal)
    (hspectral : SpectralDecompositionBound transferSignal lambda C)
    (hanalytic : AnalyticPerronBranch lambda)
    (hcurvature : UniformCurvatureLowerBound lambda resonanceSet K c) :
    (∀ m θ, ‖exponentialSum legalWords valuation m θ‖ ≤ C * |lambda θ| ^ m) ∧
      ∀ ⦃θ : ℝ⦄, θ ∈ K →
        Real.log |lambda θ| ≤ Real.log (lambda 0) - c * Metric.infDist θ resonanceSet ^ 2 := by
  refine ⟨
    exponentialSum_bound_of_spectral_wrapper legalWords valuation transferSignal lambda C
      hwrapper hspectral,
    ?_⟩
  intro θ hθ
  have hdrop :=
    log_radius_abs_drop_of_uniform_curvature lambda resonanceSet K c hcurvature hθ
  have hlog0 : Real.log |lambda 0| = Real.log (lambda 0) := by
    rw [abs_of_pos hanalytic.2]
  simpa [hlog0] using hdrop

end Omega.Zeta
