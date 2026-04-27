import Omega.Zeta.XiTimePart9xaaWulffSchurMinimalSpectrum

open scoped BigOperators

namespace Omega.Zeta

/-- `thm:xi-time-part9ze-wulff-schur-minimal-spectrum` -/
theorem paper_xi_time_part9ze_wulff_schur_minimal_spectrum {F M : ℕ} (hF : 0 < F)
    (d : Fin F → ℕ) (hpos : ∀ i, 1 ≤ d i) (hsum : ∑ i, d i = M) :
    let b := Omega.Zeta.xiTimePart64baBalancedProfile F M
    (∀ i, b i = M / F ∨ b i = M / F + 1) ∧
      (∑ i, b i = M) ∧
      (∑ i, (b i : ℝ)^2 ≤ ∑ i, (d i : ℝ)^2) := by
  exact paper_xi_time_part9xaa_wulff_schur_minimal_spectrum hF d hpos hsum

end Omega.Zeta
