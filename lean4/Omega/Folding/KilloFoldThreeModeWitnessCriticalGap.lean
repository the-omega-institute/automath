import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic
import Omega.Folding.KilloFoldRenyi2UniformityGap

open Filter
open scoped Topology

namespace Omega.Folding

/-- The three Fourier modes retained in the witness calculation. -/
def killo_fold_three_mode_witness_critical_gap_modes (m : ℕ) : Finset ℕ :=
  {0, Nat.fib m, Nat.fib (m + 1)}

/-- The lower bound obtained by keeping only the modes `0`, `F_m`, and `F_{m+1}`. -/
noncomputable def killo_fold_three_mode_witness_critical_gap_lower_bound (m : ℕ) : ℝ :=
  (1 + killoFoldResonanceConstant ^ 2 + killoFoldResonanceConstant ^ 2) *
    ((killoFoldModulus m : ℝ)⁻¹)

/-- Concrete three-mode witness package for the positive critical collision gap. -/
def killo_fold_three_mode_witness_critical_gap_statement : Prop :=
  (∀ m : ℕ,
      0 ∈ killo_fold_three_mode_witness_critical_gap_modes m ∧
        Nat.fib m ∈ killo_fold_three_mode_witness_critical_gap_modes m ∧
        Nat.fib (m + 1) ∈ killo_fold_three_mode_witness_critical_gap_modes m) ∧
    (∀ m : ℕ,
      killo_fold_three_mode_witness_critical_gap_lower_bound m =
        killoFoldCollisionProbability m) ∧
    Tendsto
      (fun m : ℕ =>
        (killoFoldModulus m : ℝ) *
          killo_fold_three_mode_witness_critical_gap_lower_bound m)
      atTop (𝓝 (1 + 2 * killoFoldResonanceConstant ^ 2)) ∧
    Tendsto (fun m : ℕ => killoFoldRenyiTwoDivergence m) atTop (𝓝 killoFoldUniformityGap) ∧
    0 < killoFoldUniformityGap

/-- Paper label: `thm:killo-fold-three-mode-witness-critical-gap`. -/
theorem paper_killo_fold_three_mode_witness_critical_gap :
    killo_fold_three_mode_witness_critical_gap_statement := by
  rcases paper_killo_fold_renyi2_uniformity_gap with ⟨_, hlim, hgap⟩
  refine ⟨?_, ?_, ?_, hlim, hgap⟩
  · intro m
    simp [killo_fold_three_mode_witness_critical_gap_modes]
  · intro m
    simp [killo_fold_three_mode_witness_critical_gap_lower_bound,
      killoFoldCollisionProbability, two_mul, add_assoc]
  · have hscaled :
      (fun m : ℕ =>
        (killoFoldModulus m : ℝ) *
          killo_fold_three_mode_witness_critical_gap_lower_bound m) =
        fun _ : ℕ => 1 + 2 * killoFoldResonanceConstant ^ 2 := by
      funext m
      have hmod : (killoFoldModulus m : ℝ) ≠ 0 := by
        have hpos : 0 < killoFoldModulus m := by
          unfold killoFoldModulus
          exact Nat.fib_pos.mpr (by omega)
        exact ne_of_gt (by exact_mod_cast hpos)
      unfold killo_fold_three_mode_witness_critical_gap_lower_bound
      field_simp [hmod]
      ring_nf
    rw [hscaled]
    exact tendsto_const_nhds

end Omega.Folding
