import Mathlib.Tactic

/--
The finite Smith-exponent entropy sum stabilizes once the precision exceeds the
total valuation, and it is always bounded above by the total valuation.

prop:pom-hankel-stiffness-entropy-decomposition
-/
theorem paper_pom_hankel_stiffness_entropy_decomposition {d : ℕ} (vp : Fin d → ℕ) :
    (∃ K : ℕ, ∀ k ≥ K, (∑ i : Fin d, min (vp i) k) = ∑ i : Fin d, vp i) ∧
      (∀ k, (∑ i : Fin d, min (vp i) k) ≤ ∑ i : Fin d, vp i) := by
  constructor
  · refine ⟨∑ i : Fin d, vp i, ?_⟩
    intro k hk
    apply Finset.sum_congr rfl
    intro i _
    have hle_total : vp i ≤ ∑ j : Fin d, vp j := by
      exact Finset.single_le_sum (fun j _ => Nat.zero_le (vp j)) (by simp)
    exact min_eq_left (hle_total.trans hk)
  · intro k
    apply Finset.sum_le_sum
    intro i _
    exact min_le_left (vp i) k
