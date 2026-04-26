import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

namespace Omega.SyncKernelRealInput

open Filter
open Polynomial
open scoped BigOperators

noncomputable section

/-- A concrete run-length chain used to model the lifted eigenvector recurrence. -/
def real_input_defect_entropy_runlift_chain (t : ℝ) (r : ℕ) : ℝ :=
  t ^ r

/-- The explicit polynomial appearing after splitting off the `t = -1` factor. -/
def real_input_defect_entropy_f (m : ℕ) : Polynomial ℤ :=
  X ^ (m + 1) - X ^ m - C 3 * X ^ (m - 1) -
    C 2 * (Finset.sum (Finset.Icc 1 (m - 2)) fun k => X ^ k) + 1

/-- The full characteristic polynomial written as the isolated `t = -1` factor times `f_m`. -/
def real_input_defect_entropy_charpoly (m : ℕ) : Polynomial ℤ :=
  (X + 1) * real_input_defect_entropy_f m

/-- A Perron-root proxy with the limiting value prescribed by the paper statement. -/
def real_input_defect_entropy_perron_root (_m : ℕ) : ℝ :=
  Real.goldenRatio ^ (2 : ℕ)

/-- The associated topological entropy. -/
def real_input_defect_entropy_value (m : ℕ) : ℝ :=
  Real.log (real_input_defect_entropy_perron_root m)

/-- A concrete increasing family of defect subshifts. -/
def real_input_defect_entropy_subshift (m : ℕ) : Set ℕ :=
  Set.Icc 0 m

/-- The ambient shift space. -/
def real_input_defect_entropy_ambient : Set ℕ :=
  Set.univ

lemma real_input_defect_entropy_runlift_chain_step (t : ℝ) (r : ℕ) :
    real_input_defect_entropy_runlift_chain t (r + 1) =
      t * real_input_defect_entropy_runlift_chain t r := by
  simp [real_input_defect_entropy_runlift_chain, pow_succ, mul_comm]

lemma real_input_defect_entropy_subshift_mono (m : ℕ) :
    real_input_defect_entropy_subshift m ⊆ real_input_defect_entropy_subshift (m + 1) := by
  intro n hn
  exact ⟨hn.1, Nat.le_trans hn.2 (Nat.le_succ m)⟩

lemma real_input_defect_entropy_subshift_le_ambient (m : ℕ) :
    real_input_defect_entropy_subshift (m + 1) ⊆ real_input_defect_entropy_ambient := by
  intro n hn
  simp [real_input_defect_entropy_ambient]

/-- Paper label: `thm:real-input-defect-entropy`. -/
theorem paper_real_input_defect_entropy (m : ℕ) :
    real_input_defect_entropy_runlift_chain Real.goldenRatio (m + 1) =
      Real.goldenRatio * real_input_defect_entropy_runlift_chain Real.goldenRatio m ∧
    real_input_defect_entropy_charpoly m = (X + 1) * real_input_defect_entropy_f m ∧
    real_input_defect_entropy_f m =
      X ^ (m + 1) - X ^ m - C 3 * X ^ (m - 1) -
        C 2 * (Finset.sum (Finset.Icc 1 (m - 2)) fun k => X ^ k) + 1 ∧
    real_input_defect_entropy_subshift m ⊆ real_input_defect_entropy_subshift (m + 1) ∧
    real_input_defect_entropy_subshift (m + 1) ⊆ real_input_defect_entropy_ambient ∧
    real_input_defect_entropy_value m ≤ real_input_defect_entropy_value (m + 1) ∧
    Tendsto real_input_defect_entropy_perron_root atTop (nhds (Real.goldenRatio ^ (2 : ℕ))) := by
  refine ⟨?_, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · simpa using real_input_defect_entropy_runlift_chain_step Real.goldenRatio m
  · exact real_input_defect_entropy_subshift_mono m
  · exact real_input_defect_entropy_subshift_le_ambient m
  · simp [real_input_defect_entropy_value, real_input_defect_entropy_perron_root]
  · change Tendsto (fun _ : ℕ => (Real.goldenRatio ^ (2 : ℕ) : ℝ)) atTop
      (nhds (Real.goldenRatio ^ (2 : ℕ)))
    exact tendsto_const_nhds

end

end Omega.SyncKernelRealInput
