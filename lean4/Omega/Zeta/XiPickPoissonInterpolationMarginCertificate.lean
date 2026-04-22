import Omega.Zeta.PickPoissonMinSeparationLowerbound

namespace Omega.Zeta

/-- Paper label: `prop:xi-pick-poisson-interpolation-margin-certificate`. Once the Pick--Poisson
matrix has been identified as a Gram matrix, the determinant as the squared Gram volume, and
`λ_min` as the worst Rayleigh-quotient margin, the existing separation lower bound upgrades these
identities into a concrete geometric margin certificate. -/
theorem paper_xi_pick_poisson_interpolation_margin_certificate
    (κ : Nat) (detP volumeSq lambdaMin worstMargin pSigma pMax rhoMin lambdaMax : ℝ)
    (hGramDet : detP = volumeSq)
    (hRayleigh : lambdaMin = worstMargin)
    (hdet : 0 < detP) (hpSigma : 0 < pSigma) (hpMax : 0 < pMax)
    (hlambdaMin_lower : detP / pSigma ^ (κ - 1) ≤ lambdaMin)
    (hlambdaMin_upper : lambdaMin ≤ pMax * rhoMin ^ 2)
    (hlambdaMax_lower : pMax ≤ lambdaMax) :
    detP = volumeSq ∧
      lambdaMin = worstMargin ∧
      rhoMin ^ 2 ≥ detP / (pMax * pSigma ^ (κ - 1)) ∧
      lambdaMax / lambdaMin ≥ 1 / rhoMin ^ 2 := by
  obtain ⟨hsep, hcond⟩ :=
    paper_xi_pick_poisson_min_separation_lowerbound
      κ detP pSigma pMax rhoMin lambdaMax lambdaMin
      hdet hpSigma hpMax hlambdaMin_lower hlambdaMin_upper hlambdaMax_lower
  exact ⟨hGramDet, hRayleigh, hsep, hcond⟩

end Omega.Zeta
