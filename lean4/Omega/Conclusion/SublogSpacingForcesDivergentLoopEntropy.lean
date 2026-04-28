import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete sequences used in the sublog-spacing divergence criterion. -/
structure conclusion_sublog_spacing_forces_divergent_loop_entropy_data where
  kappa : ℕ → ℝ
  spacing : ℕ → ℝ

/-- The logarithmic exponent controlling the loop-entropy scale. -/
noncomputable def conclusion_sublog_spacing_forces_divergent_loop_entropy_driver
    (D : conclusion_sublog_spacing_forces_divergent_loop_entropy_data) (n : ℕ) : ℝ :=
  Real.log (D.kappa n) - 2 * D.spacing n

/-- The loop-entropy scale obtained by exponentiating the logarithmic driver. -/
noncomputable def conclusion_sublog_spacing_forces_divergent_loop_entropy_loop_entropy
    (D : conclusion_sublog_spacing_forces_divergent_loop_entropy_data) (n : ℕ) : ℝ :=
  Real.exp (conclusion_sublog_spacing_forces_divergent_loop_entropy_driver D n)

/-- Eventual unboundedness above every real threshold. -/
def conclusion_sublog_spacing_forces_divergent_loop_entropy_tends_to_infinity
    (u : ℕ → ℝ) : Prop :=
  ∀ B : ℝ, ∃ N : ℕ, ∀ n ≥ N, B ≤ u n

/-- Sublog spacing, together with divergent `log κ`, forces divergent loop entropy. -/
def conclusion_sublog_spacing_forces_divergent_loop_entropy_statement
    (D : conclusion_sublog_spacing_forces_divergent_loop_entropy_data) : Prop :=
  conclusion_sublog_spacing_forces_divergent_loop_entropy_tends_to_infinity
      (fun n => Real.log (D.kappa n)) →
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, D.spacing n ≤ ε * Real.log (D.kappa n)) →
      conclusion_sublog_spacing_forces_divergent_loop_entropy_tends_to_infinity
        (conclusion_sublog_spacing_forces_divergent_loop_entropy_loop_entropy D)

/-- Paper label: `cor:conclusion-sublog-spacing-forces-divergent-loop-entropy`. -/
theorem paper_conclusion_sublog_spacing_forces_divergent_loop_entropy
    (D : conclusion_sublog_spacing_forces_divergent_loop_entropy_data) :
    conclusion_sublog_spacing_forces_divergent_loop_entropy_statement D := by
  intro hlog hsub B
  by_cases hB : B ≤ 0
  · refine ⟨0, ?_⟩
    intro n hn
    have hpos :
        0 < conclusion_sublog_spacing_forces_divergent_loop_entropy_loop_entropy D n :=
      Real.exp_pos _
    exact le_trans hB hpos.le
  · have hBpos : 0 < B := lt_of_not_ge hB
    obtain ⟨Nsub, hNsub⟩ := hsub (1 / 4 : ℝ) (by norm_num)
    obtain ⟨Nlog, hNlog⟩ := hlog (2 * Real.log B)
    refine ⟨max Nsub Nlog, ?_⟩
    intro n hn
    have hnsub : n ≥ Nsub := le_trans (Nat.le_max_left Nsub Nlog) hn
    have hnlog : n ≥ Nlog := le_trans (Nat.le_max_right Nsub Nlog) hn
    have hspacing : D.spacing n ≤ (1 / 4 : ℝ) * Real.log (D.kappa n) :=
      hNsub n hnsub
    have hlarge : 2 * Real.log B ≤ Real.log (D.kappa n) := hNlog n hnlog
    have hdriver :
        Real.log B ≤
          conclusion_sublog_spacing_forces_divergent_loop_entropy_driver D n := by
      rw [conclusion_sublog_spacing_forces_divergent_loop_entropy_driver]
      nlinarith
    rw [conclusion_sublog_spacing_forces_divergent_loop_entropy_loop_entropy]
    calc
      B = Real.exp (Real.log B) := by rw [Real.exp_log hBpos]
      _ ≤ Real.exp
          (conclusion_sublog_spacing_forces_divergent_loop_entropy_driver D n) :=
        Real.exp_le_exp.mpr hdriver

end Omega.Conclusion
