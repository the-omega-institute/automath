import Mathlib.Data.Real.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic

namespace Omega.POM

noncomputable section

/-- Concrete restricted-domain quadratic package for the negative-temperature oracle Fenchel
duality. The pressure is written in the shifted variable `theta = q - 1`, and the chosen primal
and dual optimizers are required to lie in the corresponding restricted intervals. -/
structure pom_oracle_restricted_fenchel_duality_negative_temp_data where
  tauOne : ℝ
  sigmaSlope : ℝ
  curvature : ℝ
  thetaStar : ℝ
  thetaLeft : ℝ
  thetaRight : ℝ
  alphaLeft : ℝ
  alphaRight : ℝ
  curvature_pos : 0 < curvature
  theta_mem : thetaLeft ≤ thetaStar ∧ thetaStar ≤ thetaRight
  alpha_mem :
    alphaLeft ≤ sigmaSlope + curvature * thetaStar ∧
      sigmaSlope + curvature * thetaStar ≤ alphaRight

/-- Restricted theta-domain carrying the negative-temperature Fenchel transform. -/
def pom_oracle_restricted_fenchel_duality_negative_temp_thetaDomain
    (D : pom_oracle_restricted_fenchel_duality_negative_temp_data) : Set ℝ :=
  Set.Icc D.thetaLeft D.thetaRight

/-- Restricted dual-domain carrying the reverse Fenchel transform. -/
def pom_oracle_restricted_fenchel_duality_negative_temp_alphaDomain
    (D : pom_oracle_restricted_fenchel_duality_negative_temp_data) : Set ℝ :=
  Set.Icc D.alphaLeft D.alphaRight

/-- Distinguished dual optimizer paired with `thetaStar`. -/
def pom_oracle_restricted_fenchel_duality_negative_temp_alphaStar
    (D : pom_oracle_restricted_fenchel_duality_negative_temp_data) : ℝ :=
  D.sigmaSlope + D.curvature * D.thetaStar

/-- Distinguished oracle order after the substitution `theta = q - 1`. -/
def pom_oracle_restricted_fenchel_duality_negative_temp_qStar
    (D : pom_oracle_restricted_fenchel_duality_negative_temp_data) : ℝ :=
  D.thetaStar + 1

/-- Restricted pressure profile expressed in the original `q` variable. -/
def pom_oracle_restricted_fenchel_duality_negative_temp_tau
    (D : pom_oracle_restricted_fenchel_duality_negative_temp_data) (q : ℝ) : ℝ :=
  D.tauOne + D.sigmaSlope * (q - 1) + D.curvature / 2 * (q - 1) ^ 2

/-- Shifted pressure germ on the restricted negative-temperature theta-domain. -/
def pom_oracle_restricted_fenchel_duality_negative_temp_Sigma_orc
    (D : pom_oracle_restricted_fenchel_duality_negative_temp_data) (theta : ℝ) : ℝ :=
  D.sigmaSlope * theta + D.curvature / 2 * theta ^ 2

/-- Oracle free-energy profile rewritten through the `theta = q - 1` change of variables. -/
def pom_oracle_restricted_fenchel_duality_negative_temp_Gamma_orc
    (D : pom_oracle_restricted_fenchel_duality_negative_temp_data) (q : ℝ) : ℝ :=
  pom_oracle_restricted_fenchel_duality_negative_temp_tau D q

/-- Restricted negative-temperature conjugate on the dual interval. -/
def pom_oracle_restricted_fenchel_duality_negative_temp_Lambda_minus
    (D : pom_oracle_restricted_fenchel_duality_negative_temp_data) (alpha : ℝ) : ℝ :=
  (alpha - D.sigmaSlope) ^ 2 / (2 * D.curvature)

/-- The restricted negative-temperature oracle package records the shifted conjugacy
`Gamma_orc(q) = Sigma_orc(theta) + tau(1)` at `theta = q - 1`, the forward interval-restricted
Fenchel transform at the paired dual point, and the reverse transform at the paired primal point. -/
def pom_oracle_restricted_fenchel_duality_negative_temp_statement
    (D : pom_oracle_restricted_fenchel_duality_negative_temp_data) : Prop :=
  let theta := D.thetaStar
  let alpha := pom_oracle_restricted_fenchel_duality_negative_temp_alphaStar D
  let q := pom_oracle_restricted_fenchel_duality_negative_temp_qStar D
  pom_oracle_restricted_fenchel_duality_negative_temp_Gamma_orc D q =
      pom_oracle_restricted_fenchel_duality_negative_temp_Sigma_orc D theta + D.tauOne ∧
    sSup
        ((fun theta' : ℝ =>
            alpha * theta' -
              pom_oracle_restricted_fenchel_duality_negative_temp_Sigma_orc D theta') ''
          pom_oracle_restricted_fenchel_duality_negative_temp_thetaDomain D) =
      pom_oracle_restricted_fenchel_duality_negative_temp_Lambda_minus D alpha ∧
    sSup
        ((fun alpha' : ℝ =>
            alpha' * theta -
              pom_oracle_restricted_fenchel_duality_negative_temp_Lambda_minus D alpha') ''
          pom_oracle_restricted_fenchel_duality_negative_temp_alphaDomain D) =
      pom_oracle_restricted_fenchel_duality_negative_temp_Sigma_orc D theta

lemma pom_oracle_restricted_fenchel_duality_negative_temp_gamma_eq_sigma_add_tau_one
    (D : pom_oracle_restricted_fenchel_duality_negative_temp_data) (theta : ℝ) :
    pom_oracle_restricted_fenchel_duality_negative_temp_Gamma_orc D (theta + 1) =
      pom_oracle_restricted_fenchel_duality_negative_temp_Sigma_orc D theta + D.tauOne := by
  unfold pom_oracle_restricted_fenchel_duality_negative_temp_Gamma_orc
    pom_oracle_restricted_fenchel_duality_negative_temp_tau
    pom_oracle_restricted_fenchel_duality_negative_temp_Sigma_orc
  ring

lemma pom_oracle_restricted_fenchel_duality_negative_temp_forward_complete_square
    (D : pom_oracle_restricted_fenchel_duality_negative_temp_data) (theta : ℝ) :
    pom_oracle_restricted_fenchel_duality_negative_temp_alphaStar D * theta -
        pom_oracle_restricted_fenchel_duality_negative_temp_Sigma_orc D theta =
      pom_oracle_restricted_fenchel_duality_negative_temp_Lambda_minus D
          (pom_oracle_restricted_fenchel_duality_negative_temp_alphaStar D) -
        D.curvature / 2 * (theta - D.thetaStar) ^ 2 := by
  have hcurv_ne : D.curvature ≠ 0 := ne_of_gt D.curvature_pos
  unfold pom_oracle_restricted_fenchel_duality_negative_temp_alphaStar
    pom_oracle_restricted_fenchel_duality_negative_temp_Sigma_orc
    pom_oracle_restricted_fenchel_duality_negative_temp_Lambda_minus
  field_simp [hcurv_ne]
  ring

lemma pom_oracle_restricted_fenchel_duality_negative_temp_reverse_complete_square
    (D : pom_oracle_restricted_fenchel_duality_negative_temp_data) (alpha : ℝ) :
    alpha * D.thetaStar -
        pom_oracle_restricted_fenchel_duality_negative_temp_Lambda_minus D alpha =
      pom_oracle_restricted_fenchel_duality_negative_temp_Sigma_orc D D.thetaStar -
        (alpha - pom_oracle_restricted_fenchel_duality_negative_temp_alphaStar D) ^ 2 /
          (2 * D.curvature) := by
  have hcurv_ne : D.curvature ≠ 0 := ne_of_gt D.curvature_pos
  unfold pom_oracle_restricted_fenchel_duality_negative_temp_alphaStar
    pom_oracle_restricted_fenchel_duality_negative_temp_Sigma_orc
    pom_oracle_restricted_fenchel_duality_negative_temp_Lambda_minus
  field_simp [hcurv_ne]
  ring

/-- Paper label: `thm:pom-oracle-restricted-fenchel-duality-negative-temp`. After rewriting
`Gamma_orc(q)` as `Sigma_orc(q - 1) + tau(1)`, the quadratic restricted negative-temperature
model realizes the forward and reverse Fenchel transforms on the chosen interval-restricted primal
and dual domains. -/
theorem paper_pom_oracle_restricted_fenchel_duality_negative_temp
    (D : pom_oracle_restricted_fenchel_duality_negative_temp_data) :
    pom_oracle_restricted_fenchel_duality_negative_temp_statement D := by
  dsimp [pom_oracle_restricted_fenchel_duality_negative_temp_statement,
    pom_oracle_restricted_fenchel_duality_negative_temp_qStar]
  refine ⟨?_, ?_, ?_⟩
  · simpa using
      pom_oracle_restricted_fenchel_duality_negative_temp_gamma_eq_sigma_add_tau_one D D.thetaStar
  ·
    have hGreatest :
        IsGreatest
            ((fun theta : ℝ =>
                pom_oracle_restricted_fenchel_duality_negative_temp_alphaStar D * theta -
                  pom_oracle_restricted_fenchel_duality_negative_temp_Sigma_orc D theta) ''
              pom_oracle_restricted_fenchel_duality_negative_temp_thetaDomain D)
            (pom_oracle_restricted_fenchel_duality_negative_temp_Lambda_minus D
              (pom_oracle_restricted_fenchel_duality_negative_temp_alphaStar D)) := by
      refine ⟨?_, ?_⟩
      · refine ⟨D.thetaStar, D.theta_mem, ?_⟩
        simpa using
          pom_oracle_restricted_fenchel_duality_negative_temp_forward_complete_square D D.thetaStar
      · intro y hy
        rcases hy with ⟨theta, htheta, rfl⟩
        have hsq :=
          pom_oracle_restricted_fenchel_duality_negative_temp_forward_complete_square D theta
        have hnonneg : 0 ≤ D.curvature / 2 * (theta - D.thetaStar) ^ 2 := by
          have hhalf_nonneg : 0 ≤ D.curvature / 2 := by
            nlinarith [D.curvature_pos]
          exact mul_nonneg hhalf_nonneg (sq_nonneg _)
        linarith
    exact hGreatest.csSup_eq
  ·
    have hGreatest :
        IsGreatest
            ((fun alpha : ℝ =>
                alpha * D.thetaStar -
                  pom_oracle_restricted_fenchel_duality_negative_temp_Lambda_minus D alpha) ''
              pom_oracle_restricted_fenchel_duality_negative_temp_alphaDomain D)
            (pom_oracle_restricted_fenchel_duality_negative_temp_Sigma_orc D D.thetaStar) := by
      refine ⟨?_, ?_⟩
      · refine ⟨pom_oracle_restricted_fenchel_duality_negative_temp_alphaStar D, D.alpha_mem, ?_⟩
        simpa using
          pom_oracle_restricted_fenchel_duality_negative_temp_reverse_complete_square D
            (pom_oracle_restricted_fenchel_duality_negative_temp_alphaStar D)
      · intro y hy
        rcases hy with ⟨alpha, halpha, rfl⟩
        have hsq :=
          pom_oracle_restricted_fenchel_duality_negative_temp_reverse_complete_square D alpha
        have hnonneg :
            0 ≤
              (alpha - pom_oracle_restricted_fenchel_duality_negative_temp_alphaStar D) ^ 2 /
                (2 * D.curvature) := by
          have hden_pos : 0 < 2 * D.curvature := by
            nlinarith [D.curvature_pos]
          exact div_nonneg (sq_nonneg _) (le_of_lt hden_pos)
        linarith
    exact hGreatest.csSup_eq

end

end Omega.POM
