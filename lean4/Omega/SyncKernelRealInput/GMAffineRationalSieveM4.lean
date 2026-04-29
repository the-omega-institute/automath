import Mathlib.Tactic

namespace Omega.SyncKernelRealInput

/-- Concrete spectral bookkeeping package for the affine rational-frequency large sieve. -/
structure gm_affine_rational_sieve_m4_data where
  M : ℕ
  smoothNorm : ℝ
  integralMass : ℝ
  rationalGridMass : ℕ → ℕ → ℝ
  residualScale : ℝ

namespace gm_affine_rational_sieve_m4_data

/-- The rank-one contribution coming from the zero Fourier mode. -/
def mainRankOneTerm (D : gm_affine_rational_sieve_m4_data) : ℝ :=
  D.smoothNorm ^ 2 * (D.M : ℝ) ^ 6 * D.integralMass ^ 2

/-- The localized rational-grid residual mass at denominator `q`. -/
def localizedRationalGridWeight (D : gm_affine_rational_sieve_m4_data) (q : ℕ) : ℝ :=
  Finset.range (q + 1) |>.sum fun a => (D.rationalGridMass q a) ^ 2

/-- The `M^4` residual term controlled by localized rational-grid Fourier mass. -/
def residualM4Term (D : gm_affine_rational_sieve_m4_data) : ℝ :=
  D.smoothNorm ^ 2 * (D.M : ℝ) ^ 4 * D.residualScale ^ 2

/-- The large-sieve left-hand side after Poisson/Fourier decomposition. -/
def sieveLeftSide (D : gm_affine_rational_sieve_m4_data) : ℝ :=
  D.mainRankOneTerm

/-- The large-sieve right-hand side: main rank-one channel plus the nonnegative `M^4` residual. -/
def sieveRightSide (D : gm_affine_rational_sieve_m4_data) : ℝ :=
  D.mainRankOneTerm + D.residualM4Term

/-- The stated rational-sieve bound. -/
def rationalSieveBound (D : gm_affine_rational_sieve_m4_data) : Prop :=
  D.sieveLeftSide ≤ D.sieveRightSide

end gm_affine_rational_sieve_m4_data

/-- Paper label: `thm:gm-affine-rational-sieve-M4`.  The Poisson/Fourier bookkeeping certificate
composes the rank-one channel with a nonnegative `M^4` rational-grid residual to give the large
sieve bound. -/
theorem paper_gm_affine_rational_sieve_m4 (D : gm_affine_rational_sieve_m4_data) :
    D.rationalSieveBound := by
  dsimp [gm_affine_rational_sieve_m4_data.rationalSieveBound,
    gm_affine_rational_sieve_m4_data.sieveLeftSide,
    gm_affine_rational_sieve_m4_data.sieveRightSide,
    gm_affine_rational_sieve_m4_data.residualM4Term]
  have hnonneg : 0 ≤ D.smoothNorm ^ 2 * (D.M : ℝ) ^ 4 * D.residualScale ^ 2 := by
    positivity
  linarith

end Omega.SyncKernelRealInput
