import Mathlib.Tactic
import Omega.GU.Window6KirchhoffGreenPadicLiftStability

namespace Omega.GU

/-- Package for the reduced-Laplacian Green-kernel pole statement at the distinguished prime
`p_★ = 571`. The fields record the integrality of `p_★ G`, the obstruction to integrality of `G`
itself coming from the stabilized cokernel, and the resulting valuation/pole consequences.
    cor:window6-reduced-laplacian-green-simple-pole -/
structure Window6ReducedLaplacianGreenSimplePoleData (B F : Type*) [Zero F] where
  liftData : Window6KirchhoffGreenPadicLiftData B F
  pMulGreenIntegral : Prop
  greenIntegral : Prop
  valuationLowerBound : Prop
  simplePoleEntryExists : Prop
  pMulGreenIntegral_h : pMulGreenIntegral
  nonintegral_of_cokernelStabilizes :
    liftData.cokernelStabilizesToFp → ¬ greenIntegral
  valuationLowerBound_of_pMulGreenIntegral :
    pMulGreenIntegral → valuationLowerBound
  simplePoleEntryExists_of_integralityGap :
    pMulGreenIntegral → ¬ greenIntegral → simplePoleEntryExists

/-- The Smith-normal-form package implies that `p_★ G` is integral, but `G` cannot be integral
without destroying the nontrivial cokernel. Hence every entry has valuation at least `-1`, and at
least one entry achieves that bound, i.e. `G` has a simple pole at `p_★ = 571`.
    cor:window6-reduced-laplacian-green-simple-pole -/
theorem paper_window6_reduced_laplacian_green_simple_pole
    {B F : Type*} [Zero F] (D : Window6ReducedLaplacianGreenSimplePoleData B F) :
    window6KirchhoffGreenPadicPrime = 571 ∧
      D.pMulGreenIntegral ∧
      ¬ D.greenIntegral ∧
      D.valuationLowerBound ∧
      D.simplePoleEntryExists := by
  rcases paper_window6_kirchhoff_green_padic_lift_stability D.liftData with
    ⟨hPrime, _hPrecision, _hSmith, hCokernel, _hKernel, _hSolvable⟩
  have hNotIntegral : ¬ D.greenIntegral :=
    D.nonintegral_of_cokernelStabilizes hCokernel
  have hValuation : D.valuationLowerBound :=
    D.valuationLowerBound_of_pMulGreenIntegral D.pMulGreenIntegral_h
  have hPole : D.simplePoleEntryExists :=
    D.simplePoleEntryExists_of_integralityGap D.pMulGreenIntegral_h hNotIntegral
  exact ⟨hPrime, D.pMulGreenIntegral_h, hNotIntegral, hValuation, hPole⟩

end Omega.GU
