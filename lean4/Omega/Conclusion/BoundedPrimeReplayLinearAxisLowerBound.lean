import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Basic
import Mathlib.Tactic

open Filter
open scoped Topology

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-bounded-prime-replay-linear-axis-lower-bound`.
If the bounded-prime replay budget satisfies `log P_m ≤ A k_m log (m + 1)` and every sparse
subsequence below the critical linear slope forces the replay success to vanish, then the same
vanishing holds for every subsequence with subcritical axis density. Contrapositively, any
subsequence whose success does not vanish must violate that linear upper bound somewhere. -/
theorem paper_conclusion_bounded_prime_replay_linear_axis_lower_bound
    (A : ℝ) (hA : 0 < A) (k : ℕ → ℕ) (success logP : ℕ → ℝ)
    (hbudget : ∀ m, logP m ≤ A * (k m : ℝ) * Real.log (m + 1))
    (hstrong :
      ∀ ε > 0, ∀ s : ℕ → ℕ, StrictMono s →
        (∀ ν, logP (s ν) ≤
          A * ((((4 / 27 : ℝ) / A) - ε) * (s ν : ℝ)) * Real.log (s ν + 1)) →
          Tendsto (fun ν => success (s ν)) atTop (𝓝 0)) :
    (∀ ε > 0, ∀ s : ℕ → ℕ, StrictMono s →
      (∀ ν, (k (s ν) : ℝ) ≤ (((4 / 27 : ℝ) / A) - ε) * (s ν : ℝ)) →
        Tendsto (fun ν => success (s ν)) atTop (𝓝 0)) ∧
      (∀ ε > 0, ∀ s : ℕ → ℕ, StrictMono s →
        ¬ Tendsto (fun ν => success (s ν)) atTop (𝓝 0) →
          ∃ ν, (((4 / 27 : ℝ) / A) - ε) * (s ν : ℝ) < k (s ν)) := by
  refine ⟨?_, ?_⟩
  · intro ε hε s hs hk
    apply hstrong ε hε s hs
    intro ν
    have hlog_nonneg : 0 ≤ Real.log (s ν + 1) := by
      have hone : (1 : ℝ) ≤ (s ν : ℝ) + 1 := by
        nlinarith
      exact Real.log_nonneg hone
    have hfac_nonneg : 0 ≤ A * Real.log (s ν + 1) := by
      nlinarith [le_of_lt hA, hlog_nonneg]
    have hmul := mul_le_mul_of_nonneg_right (hk ν) hfac_nonneg
    calc
      logP (s ν) ≤ A * (k (s ν) : ℝ) * Real.log (s ν + 1) := hbudget (s ν)
      _ = (k (s ν) : ℝ) * (A * Real.log (s ν + 1)) := by ring
      _ ≤ ((((4 / 27 : ℝ) / A) - ε) * (s ν : ℝ)) * (A * Real.log (s ν + 1)) := hmul
      _ = A * ((((4 / 27 : ℝ) / A) - ε) * (s ν : ℝ)) * Real.log (s ν + 1) := by ring
  · intro ε hε s hs hnot
    by_contra hfail
    apply hnot
    apply hstrong ε hε s hs
    intro ν
    have hkν : (k (s ν) : ℝ) ≤ (((4 / 27 : ℝ) / A) - ε) * (s ν : ℝ) := by
      exact le_of_not_gt (by
        intro hgt
        exact hfail ⟨ν, hgt⟩)
    have hlog_nonneg : 0 ≤ Real.log (s ν + 1) := by
      have hone : (1 : ℝ) ≤ (s ν : ℝ) + 1 := by
        nlinarith
      exact Real.log_nonneg hone
    have hfac_nonneg : 0 ≤ A * Real.log (s ν + 1) := by
      nlinarith [le_of_lt hA, hlog_nonneg]
    have hmul := mul_le_mul_of_nonneg_right hkν hfac_nonneg
    calc
      logP (s ν) ≤ A * (k (s ν) : ℝ) * Real.log (s ν + 1) := hbudget (s ν)
      _ = (k (s ν) : ℝ) * (A * Real.log (s ν + 1)) := by ring
      _ ≤ ((((4 / 27 : ℝ) / A) - ε) * (s ν : ℝ)) * (A * Real.log (s ν + 1)) := hmul
      _ = A * ((((4 / 27 : ℝ) / A) - ε) * (s ν : ℝ)) * Real.log (s ν + 1) := by ring

end Omega.Conclusion
