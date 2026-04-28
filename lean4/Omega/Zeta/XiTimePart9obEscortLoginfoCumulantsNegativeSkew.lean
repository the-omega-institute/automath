import Mathlib.Tactic

namespace Omega.Zeta

/-- First Bernoulli cumulant for the two-point escort fiber-information limit. -/
def xi_time_part9ob_escort_loginfo_cumulants_negative_skew_bernoulli_cumulant_one
    (theta logPhi : ℝ) : ℝ :=
  -theta * logPhi

/-- Second Bernoulli cumulant for the two-point escort fiber-information limit. -/
def xi_time_part9ob_escort_loginfo_cumulants_negative_skew_bernoulli_cumulant_two
    (theta logPhi : ℝ) : ℝ :=
  logPhi ^ 2 * theta * (1 - theta)

/-- Third Bernoulli cumulant for the two-point escort fiber-information limit. -/
def xi_time_part9ob_escort_loginfo_cumulants_negative_skew_bernoulli_cumulant_three
    (theta logPhi : ℝ) : ℝ :=
  -(logPhi ^ 3) * theta * (1 - theta) * (1 - 2 * theta)

/-- Fourth Bernoulli cumulant for the two-point escort fiber-information limit. -/
def xi_time_part9ob_escort_loginfo_cumulants_negative_skew_bernoulli_cumulant_four
    (theta logPhi : ℝ) : ℝ :=
  logPhi ^ 4 * theta * (1 - theta) * (1 - 6 * theta + 6 * theta ^ 2)

lemma xi_time_part9ob_escort_loginfo_cumulants_negative_skew_third_formula
    (theta logPhi : ℝ) :
    xi_time_part9ob_escort_loginfo_cumulants_negative_skew_bernoulli_cumulant_three
        theta logPhi =
      -(logPhi ^ 3) * theta * (1 - theta) * (1 - 2 * theta) := by
  rfl

/-- Paper label: `thm:xi-time-part9ob-escort-loginfo-cumulants-negative-skew`. -/
theorem paper_xi_time_part9ob_escort_loginfo_cumulants_negative_skew
    (theta logPhi : ℝ) (hθ0 : 0 < theta) (hθ1 : theta < 1 / 2) (hlog : 0 < logPhi) :
    -(logPhi ^ 3) * theta * (1 - theta) * (1 - 2 * theta) < 0 := by
  have hlog3 : 0 < logPhi ^ 3 := pow_pos hlog 3
  have htheta_one : 0 < 1 - theta := by linarith
  have htheta_two : 0 < 1 - 2 * theta := by linarith
  have htail : 0 < theta * (1 - theta) * (1 - 2 * theta) := by positivity
  have hneg : -(logPhi ^ 3) < 0 := by linarith
  have hthird :
      xi_time_part9ob_escort_loginfo_cumulants_negative_skew_bernoulli_cumulant_three
          theta logPhi < 0 := by
    unfold xi_time_part9ob_escort_loginfo_cumulants_negative_skew_bernoulli_cumulant_three
    rw [show -(logPhi ^ 3) * theta * (1 - theta) * (1 - 2 * theta) =
        -(logPhi ^ 3) * (theta * (1 - theta) * (1 - 2 * theta)) by ring]
    exact mul_neg_of_neg_of_pos hneg htail
  simpa [xi_time_part9ob_escort_loginfo_cumulants_negative_skew_third_formula] using hthird

end Omega.Zeta
