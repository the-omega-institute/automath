import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.Zeta.XiAdamsNormRadiusSimilarityLaw

namespace Omega.Zeta

/-- The explicit transported radius attached to the Adams scale `m_star`. -/
noncomputable def xiAdamsTransportedRadius (n : ℕ) (δ rStar : ℝ) : ℝ :=
  Real.exp (-(xiAdamsMStar n δ rStar : ℝ) / xiAdamsCommonFactor n δ / 2)

/-- A fixed-radius Jensen certificate records the explicit Adams scale, the transported radius it
produces, and the resulting fixed positive Jensen floor at radius `R`. -/
def XiAdamsFixedRadiusJensenCertificate (n : ℕ) (δ rStar R : ℝ) : Prop :=
  0 < δ → 0 < rStar → rStar < 1 → rStar < R →
    let mStar := xiAdamsMStar n δ rStar
    let transportedRadius := xiAdamsTransportedRadius n δ rStar
    xiAdamsCommonFactor n δ * xiAdamsRadiusWeight rStar ≤ mStar ∧
      (mStar : ℝ) < xiAdamsCommonFactor n δ * xiAdamsRadiusWeight rStar + 1 ∧
      transportedRadius ≤ rStar ∧
      Real.log (R / rStar) ≤ Real.log (R / transportedRadius) ∧
      0 < Real.log (R / rStar)

theorem paper_xi_adams_norm_fixed_radius_jensen_certificate
    (n : ℕ) (δ rStar R : ℝ) : XiAdamsFixedRadiusJensenCertificate n δ rStar R := by
  intro hδ hrStar hrStar_lt_one hR
  dsimp [XiAdamsFixedRadiusJensenCertificate, xiAdamsTransportedRadius]
  let C := xiAdamsCommonFactor n δ
  let w := xiAdamsRadiusWeight rStar
  let mStar := xiAdamsMStar n δ rStar
  have hC : 0 < C := by
    simpa [C] using xiAdamsCommonFactor_pos n hδ
  have hsandwich := xiAdamsMStar_sandwich n hδ hrStar hrStar_lt_one
  rcases hsandwich with ⟨hlower, hupper⟩
  have hw_le : w ≤ (mStar : ℝ) / C := by
    refine (le_div_iff₀ hC).2 ?_
    simpa [C, w, mStar, mul_comm] using hlower
  have hneg' :
      -((mStar : ℝ) / C) / 2 ≤ -w / 2 := by
    linarith
  have hneg :
      -(mStar : ℝ) / C / 2 ≤ -w / 2 := by
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hneg'
  have htransport_exp :
      Real.exp (-(mStar : ℝ) / C / 2) ≤ Real.exp (-w / 2) := by
    exact Real.exp_le_exp.mpr hneg
  have hweight :
      xiAdamsRadiusWeight rStar = -2 * Real.log rStar := by
    unfold xiAdamsRadiusWeight
    rw [show 1 / rStar ^ 2 = (rStar ^ 2)⁻¹ by simp [one_div]]
    rw [Real.log_inv, pow_two, Real.log_mul hrStar.ne' hrStar.ne']
    ring
  have hw_eq : w = -2 * Real.log rStar := by
    simpa [w] using hweight
  have htransport_le : Real.exp (-(mStar : ℝ) / C / 2) ≤ rStar := by
    calc
      Real.exp (-(mStar : ℝ) / C / 2) ≤ Real.exp (-w / 2) := htransport_exp
      _ = Real.exp (Real.log rStar) := by rw [hw_eq]; ring_nf
      _ = rStar := Real.exp_log hrStar
  have htransport_pos : 0 < Real.exp (-(mStar : ℝ) / C / 2) := Real.exp_pos _
  have hR_pos : 0 < R := lt_trans hrStar hR
  have hratio :
      R / rStar ≤ R / Real.exp (-(mStar : ℝ) / C / 2) := by
    exact div_le_div_of_nonneg_left (le_of_lt hR_pos) htransport_pos htransport_le
  have hlog_floor :
      0 < Real.log (R / rStar) := by
    have hone_lt : 1 < R / rStar := by
      have hdiv := div_lt_div_of_pos_right hR hrStar
      simpa [hrStar.ne'] using hdiv
    exact Real.log_pos hone_lt
  refine ⟨hlower, ?_, htransport_le, ?_, hlog_floor⟩
  · simpa [C, w, mStar] using hupper
  · exact Real.log_le_log (div_pos hR_pos hrStar) hratio

end Omega.Zeta
