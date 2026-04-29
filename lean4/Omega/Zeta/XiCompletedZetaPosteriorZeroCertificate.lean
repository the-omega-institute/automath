import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete interval certificate for a posterior zero of the completed zeta model.  The
lower-Lipschitz field is the certified consequence of the derivative lower bound on the interval,
and the uniform error field is the interval error budget. -/
structure xi_completed_zeta_posterior_zero_certificate_data where
  xi_completed_zeta_posterior_zero_certificate_left : ℝ
  xi_completed_zeta_posterior_zero_certificate_right : ℝ
  xi_completed_zeta_posterior_zero_certificate_model : ℝ → ℝ
  xi_completed_zeta_posterior_zero_certificate_trueXi : ℝ → ℝ
  xi_completed_zeta_posterior_zero_certificate_center : ℝ
  xi_completed_zeta_posterior_zero_certificate_M : ℝ
  xi_completed_zeta_posterior_zero_certificate_epsilon : ℝ
  xi_completed_zeta_posterior_zero_certificate_M_pos :
    0 < xi_completed_zeta_posterior_zero_certificate_M
  xi_completed_zeta_posterior_zero_certificate_center_mem :
    xi_completed_zeta_posterior_zero_certificate_left ≤
        xi_completed_zeta_posterior_zero_certificate_center ∧
      xi_completed_zeta_posterior_zero_certificate_center ≤
        xi_completed_zeta_posterior_zero_certificate_right
  xi_completed_zeta_posterior_zero_certificate_model_center_zero :
    xi_completed_zeta_posterior_zero_certificate_model
      xi_completed_zeta_posterior_zero_certificate_center = 0
  xi_completed_zeta_posterior_zero_certificate_lowerLipschitz :
    ∀ t,
      xi_completed_zeta_posterior_zero_certificate_left ≤ t →
      t ≤ xi_completed_zeta_posterior_zero_certificate_right →
        xi_completed_zeta_posterior_zero_certificate_M *
            |t - xi_completed_zeta_posterior_zero_certificate_center| ≤
          |xi_completed_zeta_posterior_zero_certificate_model t -
            xi_completed_zeta_posterior_zero_certificate_model
              xi_completed_zeta_posterior_zero_certificate_center|
  xi_completed_zeta_posterior_zero_certificate_uniformError :
    ∀ t,
      xi_completed_zeta_posterior_zero_certificate_left ≤ t →
      t ≤ xi_completed_zeta_posterior_zero_certificate_right →
        |xi_completed_zeta_posterior_zero_certificate_trueXi t -
          xi_completed_zeta_posterior_zero_certificate_model t| ≤
          xi_completed_zeta_posterior_zero_certificate_epsilon
  xi_completed_zeta_posterior_zero_certificate_trueZero : ℝ
  xi_completed_zeta_posterior_zero_certificate_trueZero_mem :
    xi_completed_zeta_posterior_zero_certificate_left ≤
        xi_completed_zeta_posterior_zero_certificate_trueZero ∧
      xi_completed_zeta_posterior_zero_certificate_trueZero ≤
        xi_completed_zeta_posterior_zero_certificate_right
  xi_completed_zeta_posterior_zero_certificate_trueZero_eq :
    xi_completed_zeta_posterior_zero_certificate_trueXi
      xi_completed_zeta_posterior_zero_certificate_trueZero = 0

namespace xi_completed_zeta_posterior_zero_certificate_data

/-- The model zero is unique on the certified interval, and every true zero in the same interval
lies in the error-budget envelope around the certified model zero. -/
def statement (D : xi_completed_zeta_posterior_zero_certificate_data) : Prop :=
  (∀ t,
      D.xi_completed_zeta_posterior_zero_certificate_left ≤ t →
      t ≤ D.xi_completed_zeta_posterior_zero_certificate_right →
      D.xi_completed_zeta_posterior_zero_certificate_model t = 0 →
        t = D.xi_completed_zeta_posterior_zero_certificate_center) ∧
    (∀ t,
      D.xi_completed_zeta_posterior_zero_certificate_left ≤ t →
      t ≤ D.xi_completed_zeta_posterior_zero_certificate_right →
      D.xi_completed_zeta_posterior_zero_certificate_trueXi t = 0 →
        |t - D.xi_completed_zeta_posterior_zero_certificate_center| ≤
          D.xi_completed_zeta_posterior_zero_certificate_epsilon /
            D.xi_completed_zeta_posterior_zero_certificate_M) ∧
    |D.xi_completed_zeta_posterior_zero_certificate_trueZero -
        D.xi_completed_zeta_posterior_zero_certificate_center| ≤
      D.xi_completed_zeta_posterior_zero_certificate_epsilon /
        D.xi_completed_zeta_posterior_zero_certificate_M

end xi_completed_zeta_posterior_zero_certificate_data

/-- Paper label: `prop:xi-completed-zeta-posterior-zero-certificate`. -/
theorem paper_xi_completed_zeta_posterior_zero_certificate
    (D : xi_completed_zeta_posterior_zero_certificate_data) : D.statement := by
  have henvelope :
      ∀ t,
        D.xi_completed_zeta_posterior_zero_certificate_left ≤ t →
        t ≤ D.xi_completed_zeta_posterior_zero_certificate_right →
        D.xi_completed_zeta_posterior_zero_certificate_trueXi t = 0 →
          |t - D.xi_completed_zeta_posterior_zero_certificate_center| ≤
            D.xi_completed_zeta_posterior_zero_certificate_epsilon /
              D.xi_completed_zeta_posterior_zero_certificate_M := by
    intro t hleft hright hzero
    have hlip :=
      D.xi_completed_zeta_posterior_zero_certificate_lowerLipschitz t hleft hright
    rw [D.xi_completed_zeta_posterior_zero_certificate_model_center_zero] at hlip
    rw [sub_zero] at hlip
    have herror :=
      D.xi_completed_zeta_posterior_zero_certificate_uniformError t hleft hright
    rw [hzero, zero_sub, abs_neg] at herror
    have hmul :
        D.xi_completed_zeta_posterior_zero_certificate_M *
            |t - D.xi_completed_zeta_posterior_zero_certificate_center| ≤
          D.xi_completed_zeta_posterior_zero_certificate_epsilon := by
      exact le_trans hlip herror
    rw [le_div_iff₀ D.xi_completed_zeta_posterior_zero_certificate_M_pos]
    simpa [mul_comm] using hmul
  refine ⟨?_, henvelope, ?_⟩
  · intro t hleft hright hmodel
    have hlip :=
      D.xi_completed_zeta_posterior_zero_certificate_lowerLipschitz t hleft hright
    rw [hmodel, D.xi_completed_zeta_posterior_zero_certificate_model_center_zero,
      sub_self, abs_zero] at hlip
    have habs_nonneg :
        0 ≤ |t - D.xi_completed_zeta_posterior_zero_certificate_center| :=
      abs_nonneg _
    have hdist_zero :
        |t - D.xi_completed_zeta_posterior_zero_certificate_center| = 0 := by
      nlinarith [D.xi_completed_zeta_posterior_zero_certificate_M_pos]
    exact sub_eq_zero.mp (abs_eq_zero.mp hdist_zero)
  · exact henvelope
      D.xi_completed_zeta_posterior_zero_certificate_trueZero
      D.xi_completed_zeta_posterior_zero_certificate_trueZero_mem.1
      D.xi_completed_zeta_posterior_zero_certificate_trueZero_mem.2
      D.xi_completed_zeta_posterior_zero_certificate_trueZero_eq

end Omega.Zeta
