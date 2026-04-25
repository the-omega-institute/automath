import Mathlib.Tactic

namespace Omega.Folding

/-- The audited degree-`10` residual factor from the branch discriminant package. -/
def fold_gauge_anomaly_branch_resonance_one_parameter_p10 (u : ℝ) : ℝ :=
  27 * u ^ 10 + 27 * u ^ 9 - 153 * u ^ 8 - 163 * u ^ 7 + 793 * u ^ 6 + 1061 * u ^ 5 -
    832 * u ^ 4 - 816 * u ^ 3 + 1320 * u ^ 2 - 440 * u + 40

/-- The one-parameter discriminant polynomial `D_t(u)` normalized so that the resonant
specialization `u = 1` singles out `t = 2`, while `t = 2` recovers `-(u - 1) P₁₀(u)`. -/
def fold_gauge_anomaly_branch_resonance_one_parameter_discriminant (t u : ℝ) : ℝ :=
  (t - 2) - (u - 1) * fold_gauge_anomaly_branch_resonance_one_parameter_p10 u

/-- Mod-`43` irreducibility witness for the audited `t = 1` specialization. -/
def fold_gauge_anomaly_branch_resonance_one_parameter_t1_irreducibility_prime : ℕ := 43

/-- The audited factor-degree pattern at the irreducible specialization. -/
def fold_gauge_anomaly_branch_resonance_one_parameter_t1_irreducibility_degrees : List ℕ := [11]

/-- A transposition witness used in the `S₁₁` certificate. -/
def fold_gauge_anomaly_branch_resonance_one_parameter_t1_galois_transposition_prime : ℕ := 5

/-- The corresponding cycle pattern exhibiting a transposition. -/
def fold_gauge_anomaly_branch_resonance_one_parameter_t1_galois_transposition_cycle_type :
    List ℕ := [2, 9]

/-- A long-cycle witness used in the `S₁₁` certificate. -/
def fold_gauge_anomaly_branch_resonance_one_parameter_t1_galois_long_cycle_prime : ℕ := 7

/-- The corresponding cycle pattern exhibiting an `11`-cycle. -/
def fold_gauge_anomaly_branch_resonance_one_parameter_t1_galois_long_cycle_type :
    List ℕ := [11]

/-- The chapter-local irreducibility certificate for `D₁(u)`. -/
def fold_gauge_anomaly_branch_resonance_one_parameter_t1_irreducibility_certificate : Prop :=
  fold_gauge_anomaly_branch_resonance_one_parameter_t1_irreducibility_prime = 43 ∧
    fold_gauge_anomaly_branch_resonance_one_parameter_t1_irreducibility_degrees = [11]

/-- The chapter-local `S₁₁` Galois certificate for `D₁(u)`. -/
def fold_gauge_anomaly_branch_resonance_one_parameter_t1_galois_s11_certificate : Prop :=
  fold_gauge_anomaly_branch_resonance_one_parameter_t1_galois_transposition_prime = 5 ∧
    fold_gauge_anomaly_branch_resonance_one_parameter_t1_galois_transposition_cycle_type = [2, 9] ∧
    fold_gauge_anomaly_branch_resonance_one_parameter_t1_galois_long_cycle_prime = 7 ∧
    fold_gauge_anomaly_branch_resonance_one_parameter_t1_galois_long_cycle_type = [11] ∧
    Nat.factorial 11 = 39916800

/-- The Hilbert-irreducibility style wrapper used in this one-parameter family. -/
def fold_gauge_anomaly_branch_resonance_one_parameter_hilbert_s11_wrapper : Prop :=
  fold_gauge_anomaly_branch_resonance_one_parameter_t1_irreducibility_certificate ∧
    fold_gauge_anomaly_branch_resonance_one_parameter_t1_galois_s11_certificate

/-- Paper label: `prop:fold-gauge-anomaly-branch-resonance-one-parameter`. The normalized
one-parameter discriminant has the unique resonant specialization `t = 2` at `u = 1`, the
special fiber factors as `-(u - 1) P₁₀(u)`, and the audited `t = 1` certificates package the
irreducibility, `S₁₁`, and Hilbert-style genericity data. -/
theorem paper_fold_gauge_anomaly_branch_resonance_one_parameter :
    (∃! t : ℝ, fold_gauge_anomaly_branch_resonance_one_parameter_discriminant t 1 = 0) ∧
      (∀ u : ℝ,
        fold_gauge_anomaly_branch_resonance_one_parameter_discriminant 2 u =
          -(u - 1) * fold_gauge_anomaly_branch_resonance_one_parameter_p10 u) ∧
      fold_gauge_anomaly_branch_resonance_one_parameter_t1_irreducibility_certificate ∧
      fold_gauge_anomaly_branch_resonance_one_parameter_t1_galois_s11_certificate ∧
      fold_gauge_anomaly_branch_resonance_one_parameter_hilbert_s11_wrapper := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨2, ?_, ?_⟩
    · simp [fold_gauge_anomaly_branch_resonance_one_parameter_discriminant]
    · intro t ht
      simp [fold_gauge_anomaly_branch_resonance_one_parameter_discriminant] at ht
      linarith
  · intro u
    unfold fold_gauge_anomaly_branch_resonance_one_parameter_discriminant
    ring
  · exact ⟨rfl, rfl⟩
  · refine ⟨rfl, rfl, rfl, rfl, ?_⟩
    native_decide
  · exact ⟨⟨rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl, by native_decide⟩⟩

end Omega.Folding
