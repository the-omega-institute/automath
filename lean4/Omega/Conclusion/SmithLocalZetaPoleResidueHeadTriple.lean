import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.Zeta.SmithPrefixSufficiency

namespace Omega.Conclusion

open Omega.Zeta
open scoped BigOperators

/-- The local pole position contributed by the free-rank part. -/
def conclusion_smith_local_zeta_pole_residue_head_triple_pole (n m : ℕ) : ℕ :=
  n - m

/-- The local residue contributed by the total `p`-primary Smith mass. -/
def conclusion_smith_local_zeta_pole_residue_head_triple_residue {m : ℕ}
    (p : ℕ) (e : Fin m → ℕ) : ℝ :=
  (p : ℝ) ^ (∑ i, e i)

/-- The local head length, i.e. the maximal Smith exponent. -/
def conclusion_smith_local_zeta_pole_residue_head_triple_head {m : ℕ}
    (e : Fin m → ℕ) : ℕ :=
  smithPrefixTop e

/-- Paper label: `thm:conclusion-smith-local-zeta-pole-residue-head-triple`. -/
theorem paper_conclusion_smith_local_zeta_pole_residue_head_triple {m : ℕ}
    (n p : ℕ) (e : Fin m → ℕ) :
    let h := conclusion_smith_local_zeta_pole_residue_head_triple_head e
    conclusion_smith_local_zeta_pole_residue_head_triple_pole n m = n - m ∧
      conclusion_smith_local_zeta_pole_residue_head_triple_residue p e =
        (p : ℝ) ^ (∑ i, e i) ∧
      smithPrefixValue e h = ∑ i, e i ∧
      (∀ k : ℕ, k < h → smithPrefixValue e k < ∑ i, e i) ∧
      (∀ k : ℕ, k < h → 0 < smithPrefixDelta e (k + 1)) ∧
      smithPrefixDelta e (h + 1) = 0 := by
  dsimp [conclusion_smith_local_zeta_pole_residue_head_triple_pole,
    conclusion_smith_local_zeta_pole_residue_head_triple_residue,
    conclusion_smith_local_zeta_pole_residue_head_triple_head]
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_⟩
  · simpa using smithPrefixValue_eq_total_of_le_top e (smithPrefixTop e) le_rfl
  · intro k hk
    have hstep : smithPrefixValue e k < smithPrefixValue e (k + 1) := by
      have hk1 : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
      simpa using
        (paper_xi_smith_p_kernel_shortest_sufficient_prefix e).1 (k + 1) hk1
          (Nat.succ_le_of_lt hk)
    have hbound : smithPrefixValue e (k + 1) ≤ ∑ i, e i := by
      unfold smithPrefixValue
      refine Finset.sum_le_sum ?_
      intro i hi
      exact Nat.min_le_left (e i) (k + 1)
    exact lt_of_lt_of_le hstep hbound
  · intro k hk
    exact smithPrefixDelta_pos_of_le_top e
      (Nat.succ_le_succ (Nat.zero_le k)) (Nat.succ_le_of_lt hk)
  · rw [smithPrefixDelta_eq_sub, smithPrefix_top_plateau e]
    simp

end Omega.Conclusion
