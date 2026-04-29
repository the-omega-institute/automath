import Omega.Zeta.XiTimePart9zbhFoldpiCenteredCompletionFactorization
import Omega.Zeta.XiTimePart9zbhFoldpiPositiveTraceClassRh

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part9zbh-foldpi-arithmetic-spectral-decoupling`. -/
theorem paper_xi_time_part9zbh_foldpi_arithmetic_spectral_decoupling
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

end Omega.Zeta
