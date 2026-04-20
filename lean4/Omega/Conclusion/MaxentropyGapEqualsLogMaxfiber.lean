import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.Conclusion.MaxfiberEntropyGaugeFourmodeRigidity

namespace Omega.Conclusion

open scoped BigOperators
open Finset

private theorem maxFiberSize_pos {n : ℕ} (hn : 0 < n) (d : Fin n → ℕ) (hd : ∀ i, 0 < d i) :
    0 < (maxFiberSize d : ℝ) := by
  let i0 : Fin n := ⟨0, hn⟩
  have hdi : d i0 ≤ maxFiberSize d := Finset.le_sup (by simp)
  have hdi' : (d i0 : ℝ) ≤ (maxFiberSize d : ℝ) := by exact_mod_cast hdi
  exact lt_of_lt_of_le (by exact_mod_cast hd i0) hdi'

set_option maxHeartbeats 400000 in
/-- Paper-facing max-entropy gap law: every fiberwise conditional-entropy decomposition is
bounded by the logarithm of the largest fiber, and equality is attained by concentrating the outer
distribution on a maximizing fiber and choosing the fiberwise uniform law there.
    thm:conclusion-maxentropy-gap-equals-log-maxfiber -/
theorem paper_conclusion_maxentropy_gap_equals_log_maxfiber :
    ∀ {n : ℕ} (hn : 0 < n) (d : Fin n → ℕ) (hd : ∀ i, 0 < d i),
      (∀ (π : Fin n → ℝ) (fiberEntropy : Fin n → ℝ),
        (∀ i, 0 ≤ π i) →
        (∑ i, π i = 1) →
        (∀ i, fiberEntropy i ≤ Real.log (d i : ℝ)) →
        ∑ i, π i * fiberEntropy i ≤ Real.log (maxFiberSize d : ℝ)) ∧
      ∃ i : Fin n,
        d i = maxFiberSize d ∧
          let π : Fin n → ℝ := fun j => if j = i then 1 else 0
          let fiberEntropy : Fin n → ℝ := fun j => if j = i then Real.log (d i : ℝ) else 0
          ∑ j, π j * fiberEntropy j = Real.log (maxFiberSize d : ℝ) := by
  intro n hn d hd
  classical
  refine ⟨?_, ?_⟩
  · intro π fiberEntropy hπ hsum hEntropy
    have hterm :
        ∀ i, π i * fiberEntropy i ≤ π i * Real.log (maxFiberSize d : ℝ) := by
      intro i
      have hdi_le : (d i : ℝ) ≤ (maxFiberSize d : ℝ) := by
        exact_mod_cast Finset.le_sup (by simp)
      have hlog_le : Real.log (d i : ℝ) ≤ Real.log (maxFiberSize d : ℝ) :=
        Real.log_le_log (by exact_mod_cast hd i) hdi_le
      exact mul_le_mul_of_nonneg_left (le_trans (hEntropy i) hlog_le) (hπ i)
    calc
      ∑ i, π i * fiberEntropy i ≤ ∑ i, π i * Real.log (maxFiberSize d : ℝ) := by
        exact Finset.sum_le_sum fun i _ => hterm i
      _ = (∑ i, π i) * Real.log (maxFiberSize d : ℝ) := by
        simpa using
          (Finset.sum_mul (s := Finset.univ) (f := fun i : Fin n => π i)
            (a := Real.log (maxFiberSize d : ℝ))).symm
      _ = Real.log (maxFiberSize d : ℝ) := by
        rw [hsum]
        ring
  · let i0 : Fin n := ⟨0, hn⟩
    obtain ⟨i, _, hi⟩ :=
      Finset.exists_mem_eq_sup (s := Finset.univ) ⟨i0, by simp⟩ d
    refine ⟨i, hi.symm, ?_⟩
    dsimp
    simp
    simpa [maxFiberSize] using (congrArg (fun t : ℕ => Real.log (t : ℝ)) hi).symm

end Omega.Conclusion
