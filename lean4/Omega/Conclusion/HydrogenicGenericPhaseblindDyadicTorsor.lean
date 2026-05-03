import Mathlib.Data.Rat.Defs
import Mathlib.Tactic
import Omega.Conclusion.HydrogenicPhaseblindAverageResidualBits
import Omega.Conclusion.HydrogenicStrictTwolevelGaugeTower
import Omega.Conclusion.HydrogenicVisibleClassRatioSplitting

namespace Omega.Conclusion

/-- Ambient hydrogenic address count in the strict two-level tower. -/
def conclusion_hydrogenic_generic_phaseblind_dyadic_torsor_ambient_card (n : ℕ) : ℕ :=
  2 * n ^ 2

/-- Generic phase-blind classes: the `mu = 0` line, carrying a two-point residual fiber. -/
def conclusion_hydrogenic_generic_phaseblind_dyadic_torsor_generic_card (n : ℕ) : ℕ :=
  2 * n

/-- Rational probability of landing in the generic phase-blind dyadic torsor slice. -/
noncomputable def conclusion_hydrogenic_generic_phaseblind_dyadic_torsor_probability
    (n : ℕ) : ℚ :=
  (conclusion_hydrogenic_generic_phaseblind_dyadic_torsor_generic_card n : ℚ) /
    conclusion_hydrogenic_generic_phaseblind_dyadic_torsor_ambient_card n

/-- Concrete conclusion package for the generic phase-blind dyadic torsor count. -/
def conclusion_hydrogenic_generic_phaseblind_dyadic_torsor_statement (n : ℕ) : Prop :=
  let D : conclusion_hydrogenic_residual_audit_capacity_Data :=
    { conclusion_hydrogenic_residual_audit_capacity_n := n }
  conclusion_hydrogenic_generic_phaseblind_dyadic_torsor_ambient_card n = 2 * n ^ 2 ∧
    conclusion_hydrogenic_generic_phaseblind_dyadic_torsor_generic_card n = 2 * n ∧
    conclusion_hydrogenic_generic_phaseblind_dyadic_torsor_probability n =
      (2 * n : ℚ) / (2 * n ^ 2 : ℚ) ∧
    conclusion_hydrogenic_generic_phaseblind_dyadic_torsor_probability n = 1 / (n : ℚ) ∧
    (∀ l : Fin n,
      conclusion_hydrogenic_residual_audit_capacity_pbFiberCard D l
        ⟨0, Nat.succ_pos l.val⟩ = 2) ∧
    (∀ l : Fin n, ∀ mu : Fin (l.val + 1), 0 < (mu : ℕ) →
      conclusion_hydrogenic_residual_audit_capacity_pbFiberCard D l mu = 4) ∧
    ∀ l : Fin n, ∀ mu : Fin (l.val + 1),
      conclusion_hydrogenic_residual_audit_capacity_pbFiberCard D l mu = 2 ∨
        conclusion_hydrogenic_residual_audit_capacity_pbFiberCard D l mu = 4

/-- Paper label: `thm:conclusion-hydrogenic-generic-phaseblind-dyadic-torsor`. -/
theorem paper_conclusion_hydrogenic_generic_phaseblind_dyadic_torsor (n : ℕ) (hn : 0 < n) :
    conclusion_hydrogenic_generic_phaseblind_dyadic_torsor_statement n := by
  let D : conclusion_hydrogenic_residual_audit_capacity_Data :=
    { conclusion_hydrogenic_residual_audit_capacity_n := n }
  have hcapacity := paper_conclusion_hydrogenic_residual_audit_capacity D
  refine ⟨rfl, rfl, ?_, ?_, hcapacity.2.2.2.1, hcapacity.2.2.2.2, ?_⟩
  · unfold conclusion_hydrogenic_generic_phaseblind_dyadic_torsor_probability
      conclusion_hydrogenic_generic_phaseblind_dyadic_torsor_generic_card
      conclusion_hydrogenic_generic_phaseblind_dyadic_torsor_ambient_card
    norm_num [Nat.cast_mul, Nat.cast_pow, mul_assoc, mul_comm, mul_left_comm]
  · have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
    unfold conclusion_hydrogenic_generic_phaseblind_dyadic_torsor_probability
      conclusion_hydrogenic_generic_phaseblind_dyadic_torsor_generic_card
      conclusion_hydrogenic_generic_phaseblind_dyadic_torsor_ambient_card
    field_simp [hnq]
    norm_num [Nat.cast_mul, Nat.cast_pow, pow_two]
    ring
  · intro l mu
    by_cases hmu : (mu : ℕ) = 0
    · left
      simp [conclusion_hydrogenic_residual_audit_capacity_pbFiberCard, hmu]
    · right
      simp [conclusion_hydrogenic_residual_audit_capacity_pbFiberCard, hmu]

end Omega.Conclusion
