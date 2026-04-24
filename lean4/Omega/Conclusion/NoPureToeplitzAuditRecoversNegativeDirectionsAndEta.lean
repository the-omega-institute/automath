import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Omega.Conclusion.ToeplitzGaugeBlindnessZeroDimensionalLedgerNecessity
import Omega.Conclusion.ToeplitzNegativeGeometryStrictificationOrthogonalSplit

namespace Omega.Conclusion

/-- Paper-facing impossibility statement: a pure Toeplitz audit can still witness the negative
Toeplitz direction, but it cannot distinguish the strictification parameter `η`. -/
def conclusion_no_pure_toeplitz_audit_recovers_negative_directions_and_eta_statement : Prop :=
  ∀ {β : Type*} (audit : (ℂ → ℂ) → β),
    toeplitzAuditFactorsThroughKernel audit →
    ∀ {κ : ℕ} (σ v : Fin κ → ℝ) (C : ℂ → ℂ) (η : ℝ),
      (∃ i, σ i * v i ≠ 0) →
        toeplitzNegativeWitness σ v < 0 ∧
          ∃ η' : ℝ,
            η' ≠ η ∧
              audit (toeplitzGaugeShift C η') = audit (toeplitzGaugeShift C η)

/-- Paper label:
`cor:conclusion-no-pure-toeplitz-audit-recovers-negative-directions-and-eta`. The negative
direction is explicitly visible through the Toeplitz negative witness, but every audit that factors
only through the Toeplitz/Carath--Pick kernel remains blind to the strictification gauge. Hence no
pure Toeplitz audit can recover both the negative directions and the parameter `η`. -/
theorem paper_conclusion_no_pure_toeplitz_audit_recovers_negative_directions_and_eta :
    conclusion_no_pure_toeplitz_audit_recovers_negative_directions_and_eta_statement := by
  intro β audit hAudit κ σ v C η hnonzero
  rcases
      paper_conclusion_toeplitz_negative_geometry_strictification_orthogonal_split
        audit hAudit σ v C η hnonzero with
    ⟨_, _, _, hneg, _, _⟩
  refine ⟨hneg, η + 1, by linarith, ?_⟩
  apply hAudit
  intro w z
  rw [carathPickKernel_toeplitzGaugeShift C (η + 1) w z,
    carathPickKernel_toeplitzGaugeShift C η w z]

end Omega.Conclusion
