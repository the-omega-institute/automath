import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- Finite Pick--Poisson Schur-flux data: point weights `p_m`, one-step Schur fluxes `π_m`,
their geometric-mean witness, and the interaction-energy ledger attached to that witness. -/
structure XiPickPoissonSchurOneStepCollapseData where
  kappa : ℕ
  hkappa : 0 < kappa
  pointWeight : Fin kappa → ℝ
  schurFlux : Fin kappa → ℝ
  geometricMeanEta : ℝ
  interactionEnergy : ℝ
  witness : Fin kappa
  pointWeight_pos : ∀ m, 0 < pointWeight m
  schurFlux_pos : ∀ m, 0 < schurFlux m
  geometricMeanEta_pos : 0 < geometricMeanEta
  geometricMeanEta_le_witness :
    geometricMeanEta ≤ pointWeight witness / schurFlux witness
  interactionEnergy_eq :
    interactionEnergy = (kappa : ℝ) * Real.log geometricMeanEta

/-- The multiplicative collapse factor coming from the geometric mean of `η_m = p_m / π_m`. -/
def xiPickPoissonCollapseFactor (D : XiPickPoissonSchurOneStepCollapseData) : ℝ :=
  1 / D.geometricMeanEta

/-- Existence of a one-step Schur-flux bottleneck in both multiplicative and negative-log
ledger form. -/
def XiPickPoissonSchurOneStepCollapseData.existsCollapseWitness
    (D : XiPickPoissonSchurOneStepCollapseData) : Prop :=
  ∃ m : Fin D.kappa,
    D.schurFlux m ≤ D.pointWeight m * xiPickPoissonCollapseFactor D ∧
      -Real.log (D.schurFlux m) ≥
        -Real.log (D.pointWeight m) + D.interactionEnergy / D.kappa

/-- A geometric-mean witness forces one Schur step to carry at least the average interaction
energy, both multiplicatively and in negative-log ledger form.
    cor:xi-pick-poisson-schur-one-step-collapse -/
theorem paper_xi_pick_poisson_schur_one_step_collapse
    (D : XiPickPoissonSchurOneStepCollapseData) : D.existsCollapseWitness := by
  refine ⟨D.witness, ?_, ?_⟩
  ·
    have hmul :
        D.schurFlux D.witness * D.geometricMeanEta ≤ D.pointWeight D.witness := by
      calc
        D.schurFlux D.witness * D.geometricMeanEta
            ≤ D.schurFlux D.witness * (D.pointWeight D.witness / D.schurFlux D.witness) := by
              exact mul_le_mul_of_nonneg_left D.geometricMeanEta_le_witness
                (le_of_lt (D.schurFlux_pos D.witness))
        _ = D.pointWeight D.witness := by
          field_simp [ne_of_gt (D.schurFlux_pos D.witness)]
    have hdiv' :
        D.schurFlux D.witness * D.geometricMeanEta / D.geometricMeanEta ≤
          D.pointWeight D.witness / D.geometricMeanEta := by
      exact div_le_div_of_nonneg_right hmul (le_of_lt D.geometricMeanEta_pos)
    have hdiv : D.schurFlux D.witness ≤ D.pointWeight D.witness / D.geometricMeanEta := by
      simpa [div_eq_mul_inv, D.geometricMeanEta_pos.ne', mul_assoc, mul_left_comm, mul_comm]
        using hdiv'
    calc
      D.schurFlux D.witness ≤ D.pointWeight D.witness / D.geometricMeanEta := hdiv
      _ = D.pointWeight D.witness * xiPickPoissonCollapseFactor D := by
        simp [xiPickPoissonCollapseFactor, div_eq_mul_inv, mul_comm]
  · have hEtaPos : 0 < D.pointWeight D.witness / D.schurFlux D.witness := by
      exact div_pos (D.pointWeight_pos D.witness) (D.schurFlux_pos D.witness)
    have hlog :
        Real.log D.geometricMeanEta ≤
          Real.log (D.pointWeight D.witness / D.schurFlux D.witness) := by
      exact Real.log_le_log D.geometricMeanEta_pos D.geometricMeanEta_le_witness
    have hkappa_pos : 0 < (D.kappa : ℝ) := by
      exact_mod_cast D.hkappa
    have hkappa_ne : (D.kappa : ℝ) ≠ 0 := ne_of_gt hkappa_pos
    have henergy :
        D.interactionEnergy / D.kappa = Real.log D.geometricMeanEta := by
      rw [D.interactionEnergy_eq]
      field_simp [hkappa_ne]
    have havg :
        D.interactionEnergy / D.kappa ≤
          Real.log (D.pointWeight D.witness / D.schurFlux D.witness) := by
      simpa [henergy] using hlog
    have havg' :
        D.interactionEnergy / D.kappa ≤
          Real.log (D.pointWeight D.witness) - Real.log (D.schurFlux D.witness) := by
      simpa [Real.log_div (ne_of_gt (D.pointWeight_pos D.witness))
        (ne_of_gt (D.schurFlux_pos D.witness))] using havg
    have htarget :
        D.interactionEnergy / D.kappa ≤
          -Real.log (D.schurFlux D.witness) + Real.log (D.pointWeight D.witness) := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using havg'
    linarith

end
end Omega.Zeta
