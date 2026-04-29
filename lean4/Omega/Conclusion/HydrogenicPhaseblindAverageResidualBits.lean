import Mathlib.Data.Rat.Defs
import Mathlib.Tactic
import Omega.Conclusion.HydrogenicResidualAuditCapacity

namespace Omega.Conclusion

/-- The number of phase-blind classes with the spin-only fiber. -/
def conclusion_hydrogenic_phaseblind_average_residual_bits_two_fiber_class_count
    (n : ℕ) : ℕ :=
  n

/-- The number of phase-blind classes with the sign-spin fiber. -/
def conclusion_hydrogenic_phaseblind_average_residual_bits_four_fiber_class_count
    (n : ℕ) : ℕ :=
  n * (n - 1) / 2

/-- Rational finite-count expression for the average residual bit budget. -/
noncomputable def conclusion_hydrogenic_phaseblind_average_residual_bits_average
    (n : ℕ) : ℚ :=
  (n : ℚ) * (1 / (n : ℚ) ^ 2) * 1 +
    ((n : ℚ) * ((n : ℚ) - 1) / 2) * (2 / (n : ℚ) ^ 2) * 2

/-- Concrete statement for the phase-blind average residual-bit formula. -/
def conclusion_hydrogenic_phaseblind_average_residual_bits_statement (n : ℕ) : Prop :=
  let D : conclusion_hydrogenic_residual_audit_capacity_Data :=
    { conclusion_hydrogenic_residual_audit_capacity_n := n }
  (∀ l : Fin n,
      conclusion_hydrogenic_residual_audit_capacity_pbFiberCard D l
        ⟨0, Nat.succ_pos l.val⟩ = 2) ∧
    (∀ l : Fin n,
      ∀ mu : Fin (l.val + 1),
        0 < (mu : ℕ) →
          conclusion_hydrogenic_residual_audit_capacity_pbFiberCard D l mu = 4) ∧
    conclusion_hydrogenic_phaseblind_average_residual_bits_two_fiber_class_count n = n ∧
    conclusion_hydrogenic_phaseblind_average_residual_bits_four_fiber_class_count n =
      n * (n - 1) / 2 ∧
    conclusion_hydrogenic_phaseblind_average_residual_bits_average n = 2 - 1 / (n : ℚ)

/-- Paper label: `thm:conclusion-hydrogenic-phaseblind-average-residual-bits`. -/
theorem paper_conclusion_hydrogenic_phaseblind_average_residual_bits
    (n : ℕ) (hn : 0 < n) :
    conclusion_hydrogenic_phaseblind_average_residual_bits_statement n := by
  let D : conclusion_hydrogenic_residual_audit_capacity_Data :=
    { conclusion_hydrogenic_residual_audit_capacity_n := n }
  have hcapacity := paper_conclusion_hydrogenic_residual_audit_capacity D
  refine ⟨hcapacity.2.2.2.1, hcapacity.2.2.2.2, rfl, rfl, ?_⟩
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold conclusion_hydrogenic_phaseblind_average_residual_bits_average
  field_simp [hnq]
  ring

end Omega.Conclusion
