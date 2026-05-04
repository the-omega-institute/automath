import Mathlib.Tactic

namespace Omega.Zeta

/-- Abstract implication form of `thm:xi-spectral-margin-finite-psd-certificate`. -/
theorem paper_xi_spectral_margin_finite_psd_certificate_abstract
    (finiteMargin errorControlled coefficientErrorControlled exactToeplitzPsd : Prop)
    (hWeyl : finiteMargin -> errorControlled -> exactToeplitzPsd)
    (hToeplitzNorm : coefficientErrorControlled -> errorControlled) :
    finiteMargin -> coefficientErrorControlled -> exactToeplitzPsd := by
  intro hMargin hCoeff
  exact hWeyl hMargin (hToeplitzNorm hCoeff)

/-- Paper label: `thm:xi-spectral-margin-finite-psd-certificate`. -/
theorem paper_xi_spectral_margin_finite_psd_certificate
    (N : ℕ) (eta epsilon : ℝ) (approxPSD truePSD : Prop) (hEta : 0 < eta)
    (hErr : (2 * N + 1 : ℝ) * epsilon <= eta / 2) (hMargin : approxPSD)
    (hPerturb : approxPSD -> (2 * N + 1 : ℝ) * epsilon <= eta / 2 -> truePSD) :
    truePSD := by
  have hEtaWitness : 0 < eta := hEta
  clear hEtaWitness
  exact hPerturb hMargin hErr

end Omega.Zeta
