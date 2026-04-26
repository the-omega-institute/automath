import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Folding.KilloFoldBinEscortRenyiLogisticGeometry

namespace Omega.Zeta

/-- The logistic natural parameter used in the escort Bernoulli limit. -/
noncomputable def xi_time_part9s_escort_logistic_expfamily_bregman_eta (q : ℝ) : ℝ :=
  -(q + 1) * Real.log Real.goldenRatio

/-- The Bernoulli log-partition function `A(η) = log (1 + exp η)`. -/
noncomputable def xi_time_part9s_escort_logistic_expfamily_bregman_A (η : ℝ) : ℝ :=
  Real.log (1 + Real.exp η)

/-- The Bernoulli/logistic Bregman form of the escort KL limit. -/
noncomputable def xi_time_part9s_escort_logistic_expfamily_bregman_B
    (p q : ℝ) : ℝ :=
  xi_time_part9s_escort_logistic_expfamily_bregman_A
      (xi_time_part9s_escort_logistic_expfamily_bregman_eta p) -
    xi_time_part9s_escort_logistic_expfamily_bregman_A
      (xi_time_part9s_escort_logistic_expfamily_bregman_eta q) -
    Omega.Folding.killoEscortTheta q *
      (xi_time_part9s_escort_logistic_expfamily_bregman_eta p -
        xi_time_part9s_escort_logistic_expfamily_bregman_eta q)

lemma xi_time_part9s_escort_logistic_expfamily_bregman_theta_closed
    (q : ℝ) :
    Omega.Folding.killoEscortTheta q =
      Real.exp (xi_time_part9s_escort_logistic_expfamily_bregman_eta q) /
        (1 + Real.exp (xi_time_part9s_escort_logistic_expfamily_bregman_eta q)) := by
  have hexp :
      Real.exp (xi_time_part9s_escort_logistic_expfamily_bregman_eta q) =
        (Real.exp ((q + 1) * Real.log Real.goldenRatio))⁻¹ := by
    rw [show xi_time_part9s_escort_logistic_expfamily_bregman_eta q =
        -((q + 1) * Real.log Real.goldenRatio) by
          unfold xi_time_part9s_escort_logistic_expfamily_bregman_eta
          ring]
    rw [Real.exp_neg]
  rw [hexp]
  unfold Omega.Folding.killoEscortTheta
  have hne : (Real.exp ((q + 1) * Real.log Real.goldenRatio) : ℝ) ≠ 0 := by
    positivity
  field_simp [hne]
  ring

lemma xi_time_part9s_escort_logistic_expfamily_bregman_eta_logit
    (q : ℝ) :
    xi_time_part9s_escort_logistic_expfamily_bregman_eta q =
      Real.log
        (Omega.Folding.killoEscortTheta q / (1 - Omega.Folding.killoEscortTheta q)) := by
  have htheta :=
    xi_time_part9s_escort_logistic_expfamily_bregman_theta_closed q
  have hratio :
      Omega.Folding.killoEscortTheta q / (1 - Omega.Folding.killoEscortTheta q) =
        Real.exp (xi_time_part9s_escort_logistic_expfamily_bregman_eta q) := by
    have hne :
        (1 + Real.exp (xi_time_part9s_escort_logistic_expfamily_bregman_eta q) : ℝ) ≠ 0 := by
      positivity
    rw [htheta]
    field_simp [hne]
    ring
  rw [hratio, Real.log_exp]

lemma xi_time_part9s_escort_logistic_expfamily_bregman_A_closed
    (q : ℝ) :
    xi_time_part9s_escort_logistic_expfamily_bregman_A
        (xi_time_part9s_escort_logistic_expfamily_bregman_eta q) =
      -Real.log (1 - Omega.Folding.killoEscortTheta q) := by
  have htheta := xi_time_part9s_escort_logistic_expfamily_bregman_theta_closed q
  have hone :
      1 - Omega.Folding.killoEscortTheta q =
        (1 + Real.exp (xi_time_part9s_escort_logistic_expfamily_bregman_eta q))⁻¹ := by
    have hne :
        (1 + Real.exp (xi_time_part9s_escort_logistic_expfamily_bregman_eta q) : ℝ) ≠ 0 := by
      positivity
    rw [htheta]
    field_simp [hne]
    ring
  have h1θ_pos : 0 < 1 - Omega.Folding.killoEscortTheta q := by
    exact sub_pos.mpr (Omega.Folding.killoEscortTheta_lt_one q)
  have hone_inv :
      (1 - Omega.Folding.killoEscortTheta q)⁻¹ =
        1 + Real.exp (xi_time_part9s_escort_logistic_expfamily_bregman_eta q) := by
    rw [hone]
    field_simp
  calc
    xi_time_part9s_escort_logistic_expfamily_bregman_A
        (xi_time_part9s_escort_logistic_expfamily_bregman_eta q)
        = Real.log ((1 - Omega.Folding.killoEscortTheta q)⁻¹) := by
            unfold xi_time_part9s_escort_logistic_expfamily_bregman_A
            rw [hone_inv]
    _ = -Real.log (1 - Omega.Folding.killoEscortTheta q) := by
          rw [Real.log_inv]

lemma xi_time_part9s_escort_logistic_expfamily_bregman_kl_eq_B
    (p q : ℝ) :
    Omega.Folding.killoEscortKLDivergence p q =
      xi_time_part9s_escort_logistic_expfamily_bregman_B p q := by
  have hθp : 0 < Omega.Folding.killoEscortTheta p :=
    Omega.Folding.killoEscortTheta_pos p
  have hθq : 0 < Omega.Folding.killoEscortTheta q :=
    Omega.Folding.killoEscortTheta_pos q
  have h1θp : 0 < 1 - Omega.Folding.killoEscortTheta p := by
    exact sub_pos.mpr (Omega.Folding.killoEscortTheta_lt_one p)
  have h1θq : 0 < 1 - Omega.Folding.killoEscortTheta q := by
    exact sub_pos.mpr (Omega.Folding.killoEscortTheta_lt_one q)
  have hBsplit :
      xi_time_part9s_escort_logistic_expfamily_bregman_B p q =
        (Omega.Folding.killoEscortTheta q * Real.log (Omega.Folding.killoEscortTheta q) -
            Omega.Folding.killoEscortTheta q * Real.log (Omega.Folding.killoEscortTheta p)) +
          ((1 - Omega.Folding.killoEscortTheta q) *
              Real.log (1 - Omega.Folding.killoEscortTheta q) -
            (1 - Omega.Folding.killoEscortTheta q) *
              Real.log (1 - Omega.Folding.killoEscortTheta p)) := by
    unfold xi_time_part9s_escort_logistic_expfamily_bregman_B
    rw [xi_time_part9s_escort_logistic_expfamily_bregman_A_closed,
      xi_time_part9s_escort_logistic_expfamily_bregman_A_closed,
      xi_time_part9s_escort_logistic_expfamily_bregman_eta_logit,
      xi_time_part9s_escort_logistic_expfamily_bregman_eta_logit]
    rw [Real.log_div hθp.ne' h1θp.ne', Real.log_div hθq.ne' h1θq.ne']
    ring
  have hθterm :
      Omega.Folding.killoEscortTheta q *
          Real.log (Omega.Folding.killoEscortTheta q / Omega.Folding.killoEscortTheta p) =
        Omega.Folding.killoEscortTheta q * Real.log (Omega.Folding.killoEscortTheta q) -
          Omega.Folding.killoEscortTheta q * Real.log (Omega.Folding.killoEscortTheta p) := by
    rw [Real.log_div hθq.ne' hθp.ne']
    ring
  have h1θterm :
      (1 - Omega.Folding.killoEscortTheta q) *
          Real.log ((1 - Omega.Folding.killoEscortTheta q) / (1 - Omega.Folding.killoEscortTheta p)) =
        (1 - Omega.Folding.killoEscortTheta q) * Real.log (1 - Omega.Folding.killoEscortTheta q) -
          (1 - Omega.Folding.killoEscortTheta q) * Real.log (1 - Omega.Folding.killoEscortTheta p) := by
    rw [Real.log_div h1θq.ne' h1θp.ne']
    ring
  calc
    Omega.Folding.killoEscortKLDivergence p q =
        Omega.Folding.killoEscortTheta q *
            Real.log (Omega.Folding.killoEscortTheta q / Omega.Folding.killoEscortTheta p) +
          (1 - Omega.Folding.killoEscortTheta q) *
            Real.log ((1 - Omega.Folding.killoEscortTheta q) / (1 - Omega.Folding.killoEscortTheta p)) := by
              rfl
    _ =
        (Omega.Folding.killoEscortTheta q * Real.log (Omega.Folding.killoEscortTheta q) -
            Omega.Folding.killoEscortTheta q * Real.log (Omega.Folding.killoEscortTheta p)) +
          ((1 - Omega.Folding.killoEscortTheta q) *
              Real.log (1 - Omega.Folding.killoEscortTheta q) -
            (1 - Omega.Folding.killoEscortTheta q) *
              Real.log (1 - Omega.Folding.killoEscortTheta p)) := by
                rw [hθterm, h1θterm]
    _ = xi_time_part9s_escort_logistic_expfamily_bregman_B p q := by
          symm
          exact hBsplit

/-- Paper label: `thm:xi-time-part9s-escort-logistic-expfamily-bregman`. The folding-side escort
Bernoulli limit can be rewritten in the logistic `η`-chart, the KL limit is exactly the Bernoulli
Bregman divergence of the log-partition function `A`, and the Fisher information is the closed
quadratic coefficient already recorded for the one-bit logistic curve. -/
theorem paper_xi_time_part9s_escort_logistic_expfamily_bregman :
    (∀ q : ℝ,
      Omega.Folding.killoEscortTheta q =
        Real.exp (xi_time_part9s_escort_logistic_expfamily_bregman_eta q) /
          (1 + Real.exp (xi_time_part9s_escort_logistic_expfamily_bregman_eta q))) ∧
      (∀ p q : ℝ,
        Omega.Folding.killoEscortKLDivergence p q =
          xi_time_part9s_escort_logistic_expfamily_bregman_B p q) ∧
      (∀ q : ℝ,
        Omega.Folding.killoEscortFisher q =
          (Real.log Real.goldenRatio) ^ 2 * Omega.Folding.killoEscortTheta q *
            (1 - Omega.Folding.killoEscortTheta q)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro q
    exact xi_time_part9s_escort_logistic_expfamily_bregman_theta_closed q
  · intro p q
    exact xi_time_part9s_escort_logistic_expfamily_bregman_kl_eq_B p q
  · intro q
    exact Omega.Folding.killoEscortFisher_closed_form q

end Omega.Zeta
