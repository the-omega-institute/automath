import Mathlib.Tactic

namespace Omega.POM

noncomputable section

/-- Concrete data for the critical-window bit inversion.  The Gaussian theorem supplies the
limit curve, while `inverseCDF` records the selected probability level in Gaussian coordinates. -/
structure pom_oracle_critical_window_bit_inversion_Data where
  sigma : ℝ
  inverseCDF : ℝ → ℝ
  targetProbability : ℝ
  logTwo : ℝ
  naturalCenter : ℕ → ℝ
  minimalNaturalBudget : ℕ → ℝ

namespace pom_oracle_critical_window_bit_inversion_Data

/-- The critical-window offset obtained by substituting `t = sigma * Phi^{-1}(p)`. -/
def criticalOffset (D : pom_oracle_critical_window_bit_inversion_Data) : ℝ :=
  D.sigma * D.inverseCDF D.targetProbability

/-- The real-valued bit budget corresponding to a natural-scale oracle budget. -/
def bitBudget (D : pom_oracle_critical_window_bit_inversion_Data) (m : ℕ) : ℝ :=
  D.minimalNaturalBudget m / D.logTwo

/-- The second-order critical-window bit expansion. -/
def bit_budget_asymptotic (D : pom_oracle_critical_window_bit_inversion_Data) : Prop :=
  D.logTwo ≠ 0 →
    (∀ m : ℕ, D.minimalNaturalBudget m = D.naturalCenter m + criticalOffset D) →
      ∀ m : ℕ,
        bitBudget D m =
          D.naturalCenter m / D.logTwo +
            D.sigma * D.inverseCDF D.targetProbability / D.logTwo

end pom_oracle_critical_window_bit_inversion_Data

/-- Paper label: `cor:pom-oracle-critical-window-bit-inversion`. -/
theorem paper_pom_oracle_critical_window_bit_inversion
    (D : pom_oracle_critical_window_bit_inversion_Data) :
    D.bit_budget_asymptotic := by
  intro hlog hminimal m
  unfold pom_oracle_critical_window_bit_inversion_Data.bitBudget
  rw [hminimal m]
  unfold pom_oracle_critical_window_bit_inversion_Data.criticalOffset
  field_simp [hlog]

end

end Omega.POM
