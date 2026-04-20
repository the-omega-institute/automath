import Mathlib.Tactic

namespace Omega.POM

/-- The strict gap between the `d`-th and `(d + 1)`-st singular values in the finite-pole model.
-/
def hankelFinitePoleSpectralGap (sigmaD sigmaDplus1 : ℝ) : ℝ :=
  sigmaD - sigmaDplus1

/-- Paper-facing finite-pole Hankel spectral-gap certificate: an operator-norm upper bound on the
tail singular value together with a Vandermonde lower bound on the signal block yields a positive
gap after the Weyl transfer step.
    thm:pom-hankel-finite-pole-spectral-gap -/
theorem paper_pom_hankel_finite_pole_spectral_gap
    {sigmaD sigmaDplus1 opNormE vandermondeLower : ℝ} (hTail : sigmaDplus1 ≤ opNormE)
    (hSignal : vandermondeLower ≤ sigmaD) (hWeyl : opNormE < vandermondeLower) :
    0 < hankelFinitePoleSpectralGap sigmaD sigmaDplus1 := by
  dsimp [hankelFinitePoleSpectralGap]
  linarith

end Omega.POM
