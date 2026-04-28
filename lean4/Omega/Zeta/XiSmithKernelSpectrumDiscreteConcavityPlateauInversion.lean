import Omega.Zeta.SmithPrefixSufficiency

namespace Omega.Zeta

open scoped BigOperators

/-- Paper label: `cor:xi-smith-kernel-spectrum-discrete-concavity-plateau-inversion`. -/
theorem paper_xi_smith_kernel_spectrum_discrete_concavity_plateau_inversion
    {m : ℕ} (e : Fin m → ℕ) (f : ℕ → ℕ)
    (hf : ∀ k, f k = ∑ i, min k (e i)) (E : ℕ) (hE : ∀ i, e i ≤ E) :
    (∀ k, f (k + 1) - f k ≥ f (k + 2) - f (k + 1)) ∧
      (∀ k, E ≤ k → f (k + 1) = f k) := by
  have hf_prefix : ∀ k, f k = smithPrefixValue e k := by
    intro k
    simp [hf k, smithPrefixValue, Nat.min_comm]
  constructor
  · intro k
    have hstep₁ : f (k + 1) - f k = smithPrefixDelta e (k + 1) := by
      calc
        f (k + 1) - f k = smithPrefixValue e (k + 1) - smithPrefixValue e k := by
          rw [hf_prefix (k + 1), hf_prefix k]
        _ = smithPrefixDelta e (k + 1) := (smithPrefixDelta_eq_sub e k).symm
    have hstep₂ : f (k + 2) - f (k + 1) = smithPrefixDelta e (k + 2) := by
      calc
        f (k + 2) - f (k + 1) =
            smithPrefixValue e (k + 2) - smithPrefixValue e (k + 1) := by
          rw [hf_prefix (k + 2), hf_prefix (k + 1)]
        _ = smithPrefixDelta e (k + 2) := by
          simpa [Nat.add_assoc] using (smithPrefixDelta_eq_sub e (k + 1)).symm
    rw [hstep₁, hstep₂]
    unfold smithPrefixDelta
    refine Finset.sum_le_sum ?_
    intro i _
    by_cases hnext : k + 2 ≤ e i
    · have hcurr : k + 1 ≤ e i := by omega
      simp [hnext, hcurr]
    · by_cases hcurr : k + 1 ≤ e i <;> simp [hnext, hcurr]
  · intro k hk
    calc
      f (k + 1) = smithPrefixValue e (k + 1) := hf_prefix (k + 1)
      _ = ∑ i, e i := smithPrefixValue_eq_total_of_le_top e (k + 1) (by
        unfold smithPrefixTop
        refine Finset.sup_le ?_
        intro i _
        exact le_trans (hE i) (le_trans hk (Nat.le_succ k)))
      _ = smithPrefixValue e k := by
        rw [smithPrefixValue_eq_total_of_le_top e k]
        unfold smithPrefixTop
        refine Finset.sup_le ?_
        intro i _
        exact le_trans (hE i) hk
      _ = f k := (hf_prefix k).symm

end Omega.Zeta
