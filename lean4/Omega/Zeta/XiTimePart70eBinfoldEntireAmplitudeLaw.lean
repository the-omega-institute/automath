import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Conclusion.FoldbinLikelihoodRatioTwoAtomTransfer
import Omega.Zeta.XiTimePart70aaRealMomentInversemomentBernoulliBridge

namespace Omega.Zeta

noncomputable section

/-- The explicit entire amplitude extending the closed real-moment profile. -/
def xi_time_part70e_binfold_entire_amplitude_law_amplitude (z : ℂ) : ℂ :=
  ((Real.sqrt 5 : ℂ)⁻¹) *
    ((Real.goldenRatio : ℂ) + Complex.exp (-((Real.log Real.goldenRatio : ℂ) * z)))

/-- Paper label: `thm:xi-time-part70e-binfold-entire-amplitude-law`. The previously verified
closed formula for all real binfold moments supplies the real-axis profile, and the same explicit
formula extends to an entire function on `ℂ`. -/
theorem paper_xi_time_part70e_binfold_entire_amplitude_law :
    (∀ q : ℕ, ∀ t : ℝ,
      Omega.Conclusion.foldbinLikelihoodRatioExpectation q (fun x => Real.rpow x t) =
        Omega.Conclusion.binfoldTwoPointLimitMassHigh Real.goldenRatio q *
          Real.rpow (Omega.Conclusion.foldbinLikelihoodRatioLow q) t +
        Omega.Conclusion.binfoldTwoPointLimitMassLow Real.goldenRatio q *
          Real.rpow (Omega.Conclusion.foldbinLikelihoodRatioHigh q) t) ∧
      AnalyticOnNhd ℂ xi_time_part70e_binfold_entire_amplitude_law_amplitude Set.univ ∧
      ∀ z : ℂ,
        xi_time_part70e_binfold_entire_amplitude_law_amplitude z =
          ((Real.sqrt 5 : ℂ)⁻¹) *
            ((Real.goldenRatio : ℂ) + Complex.exp (-((Real.log Real.goldenRatio : ℂ) * z))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro q t
    exact (paper_xi_time_part70aa_binfold_all_real_moments_closed q t).1
  · have hd : Differentiable ℂ xi_time_part70e_binfold_entire_amplitude_law_amplitude := by
      change Differentiable ℂ
        (fun z : ℂ =>
          ((Real.sqrt 5 : ℂ)⁻¹) *
            ((Real.goldenRatio : ℂ) + Complex.exp (-((Real.log Real.goldenRatio : ℂ) * z))))
      fun_prop
    exact hd.differentiableOn.analyticOnNhd isOpen_univ
  · intro z
    rfl

end

end Omega.Zeta
