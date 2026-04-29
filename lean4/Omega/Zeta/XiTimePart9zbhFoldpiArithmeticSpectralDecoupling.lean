import Mathlib.Algebra.Ring.Defs
import Omega.Zeta.XiTimePart9zbhFoldpiCenteredCompletionFactorization
import Omega.Zeta.XiTimePart9zbhFoldpiPositiveTraceClassRh

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part9zbh-foldpi-arithmetic-spectral-decoupling`. -/
theorem xi_time_part9zbh_foldpi_arithmetic_spectral_decoupling_logical_package
    (RH CenteredFactorization PositiveTraceClassRH ArithmeticZeros SpectralZeros
      StrictMultiplicativeDecoupling : Prop)
    (hcenter : RH -> CenteredFactorization)
    (htrace : RH -> PositiveTraceClassRH)
    (harith : CenteredFactorization -> ArithmeticZeros)
    (hspec : PositiveTraceClassRH -> SpectralZeros)
    (hdec : CenteredFactorization -> PositiveTraceClassRH -> StrictMultiplicativeDecoupling)
    (hRH : RH) :
    ArithmeticZeros ∧ SpectralZeros ∧ StrictMultiplicativeDecoupling := by
  have hCentered : CenteredFactorization := hcenter hRH
  have hTrace : PositiveTraceClassRH := htrace hRH
  exact ⟨harith hCentered, hspec hTrace, hdec hCentered hTrace⟩

/-- Paper label: `thm:xi-time-part9zbh-foldpi-arithmetic-spectral-decoupling`. -/
theorem paper_xi_time_part9zbh_foldpi_arithmetic_spectral_decoupling
    {R : Type} [CommSemiring R] (Theta A ThetaSharp theta0 detK : R)
    (hFactor : Theta = A * ThetaSharp) (hRH : ThetaSharp = theta0 * detK) :
    Theta = A * theta0 * detK := by
  calc
    Theta = A * ThetaSharp := hFactor
    _ = A * (theta0 * detK) := by rw [hRH]
    _ = A * theta0 * detK := by rw [mul_assoc]

end Omega.Zeta
