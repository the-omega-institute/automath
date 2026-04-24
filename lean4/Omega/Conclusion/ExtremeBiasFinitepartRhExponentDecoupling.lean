import Omega.Conclusion.RealInput40ZeroTempQuarticConstantUnification
import Omega.Zeta.XiTimePart9wBasicRootUnityErrorExponentToOne

open Filter Topology

namespace Omega.Conclusion

/-- Concrete data for the extreme-bias finite-part side of the decoupling theorem. -/
structure conclusion_extreme_bias_finitepart_rh_exponent_decoupling_data where
  b : ℝ
  c : ℝ
  Cinf : ℝ
  logMinf : ℝ
  hcpos : 0 < c
  hbdef : b = 1 / c ^ 2
  hroot : realInput40ZeroTempQuartic b = 0
  hresidue : Cinf = realInput40ZeroTempResidue b
  habel : logMinf = Real.log Cinf - ∑' m : ℕ, realInput40ZeroTempAbelKernel b m

/-- Publication-facing statement: the quartic finite-part package persists on the extreme-bias
side, while the root-unity error exponent still degenerates to `1`. -/
def conclusion_extreme_bias_finitepart_rh_exponent_decoupling_statement
    (D : conclusion_extreme_bias_finitepart_rh_exponent_decoupling_data) : Prop :=
  realInput40ZeroTempQuartic D.b = 0 ∧
    D.Cinf = realInput40ZeroTempResidue D.b ∧
    D.logMinf = Real.log D.Cinf - ∑' m : ℕ, realInput40ZeroTempAbelKernel D.b m ∧
    Omega.Zeta.xiTimePart9wBasicAout =
      (Real.pi ^ 2) * (8955 - 3983 * Real.sqrt 5) /
        (500 * Omega.Zeta.xiTimePart9wBasicLogLambda) ∧
    Omega.Zeta.xiTimePart9wBasicBout =
      (Real.pi ^ 4) * (1354428303 - 605718497 * Real.sqrt 5) /
        (150000 * Omega.Zeta.xiTimePart9wBasicLogLambda) ∧
    Tendsto Omega.Zeta.xiTimePart9wBasicVartheta atTop (𝓝 1)

/-- Paper label: `thm:conclusion-extreme-bias-finitepart-rh-exponent-decoupling`. -/
theorem paper_conclusion_extreme_bias_finitepart_rh_exponent_decoupling
    (D : conclusion_extreme_bias_finitepart_rh_exponent_decoupling_data) :
    conclusion_extreme_bias_finitepart_rh_exponent_decoupling_statement D := by
  have hfinitepart :=
    paper_conclusion_realinput40_zero_temp_quartic_constant_unification
      D.b D.c D.Cinf D.logMinf D.hcpos D.hbdef D.hroot D.hresidue D.habel
  have hresidue : D.Cinf = realInput40ZeroTempResidue D.b := hfinitepart.2.2.2.1
  have habel :
      D.logMinf = Real.log D.Cinf - ∑' m : ℕ, realInput40ZeroTempAbelKernel D.b m :=
    hfinitepart.2.2.2.2
  rcases Omega.Zeta.paper_xi_time_part9w_basic_root_unity_error_exponent_to_one with
    ⟨hAout, hBout, hlimit⟩
  exact ⟨hfinitepart.1, hresidue, habel, hAout, hBout, hlimit⟩

end Omega.Conclusion
