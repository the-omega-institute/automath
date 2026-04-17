import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- Paper label: `cor:xi-bulk-entropy-strict-convexity`. -/
theorem paper_xi_bulk_entropy_strict_convexity (κ : Nat) (δ : Fin κ → ℝ) (s : ℝ) (hκ : 0 < κ)
    (hδ : ∀ j, 0 < δ j) :
    0 < (((2 : ℝ) * κ - 1) *
      (∑ j : Fin κ, (Real.exp s * δ j) / (1 + Real.exp s * δ j) ^ 2)) := by
  let f : Fin κ → ℝ := fun j => (Real.exp s * δ j) / (1 + Real.exp s * δ j) ^ 2
  have hk1 : (1 : ℝ) ≤ κ := by
    exact_mod_cast Nat.succ_le_of_lt hκ
  have hpref : 0 < ((2 : ℝ) * κ - 1) := by
    nlinarith
  have hterm_pos : ∀ j : Fin κ, 0 < f j := by
    intro j
    have hnum : 0 < Real.exp s * δ j := mul_pos (Real.exp_pos s) (hδ j)
    have hbase : 0 < 1 + Real.exp s * δ j := by
      nlinarith [Real.exp_pos s, hδ j]
    have hden : 0 < (1 + Real.exp s * δ j) ^ 2 := pow_pos hbase 2
    exact div_pos hnum hden
  have hsum' : 0 < ∑ j ∈ Finset.univ, f j := by
    classical
    refine Finset.sum_pos' ?_ ?_
    · intro j _
      exact le_of_lt (hterm_pos j)
    · refine ⟨⟨0, hκ⟩, Finset.mem_univ _, hterm_pos ⟨0, hκ⟩⟩
  have hsum : 0 < ∑ j : Fin κ, f j := by
    simpa using hsum'
  simpa [f] using mul_pos hpref hsum

end Omega.Zeta
