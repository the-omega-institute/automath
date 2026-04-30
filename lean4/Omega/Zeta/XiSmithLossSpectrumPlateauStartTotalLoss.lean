import Omega.Zeta.KilloSmithLossSpectrum

namespace Omega.Zeta

/-- A finite Smith exponent multiset has a height dominating all exponents. -/
lemma xi_smith_loss_spectrum_plateau_start_total_loss_exists_bound (s : Multiset ℕ) :
    ∃ H : ℕ, ∀ v ∈ s, v ≤ H := by
  induction s using Multiset.induction with
  | empty =>
      exact ⟨0, by simp⟩
  | cons a t ih =>
      rcases ih with ⟨H, hH⟩
      refine ⟨max a H, ?_⟩
      intro v hv
      rcases Multiset.mem_cons.mp hv with rfl | hv
      · exact Nat.le_max_left v H
      · exact le_trans (hH v hv) (Nat.le_max_right _ _)

/-- Paper label: `cor:xi-smith-loss-spectrum-plateau-start-total-loss`.
The Smith loss spectrum determines the kernel-size formula, first differences, exact
multiplicities, a finite plateau height, and the total Smith loss `s.sum`. -/
theorem paper_xi_smith_loss_spectrum_plateau_start_total_loss
    (p n m : ℕ) (smithExponents : Multiset ℕ) :
    (∀ k : ℕ,
      smithFiberCardinality p n m k smithExponents =
        p ^ (k * (n - m) + smithEntropy smithExponents k)) ∧
    (∀ k : ℕ,
      smithEntropy smithExponents (k + 1) - smithEntropy smithExponents k =
        smithDelta smithExponents (k + 1)) ∧
    (∀ e : ℕ,
      (smithExponents.filter fun v => v = e).card =
        smithDelta smithExponents e - smithDelta smithExponents (e + 1)) ∧
    (∃ H : ℕ,
      (∀ v ∈ smithExponents, v ≤ H) ∧
        (∀ k : ℕ, H ≤ k → smithEntropy smithExponents k = smithExponents.sum) ∧
          smithEntropy smithExponents H = smithExponents.sum ∧
            smithEntropy smithExponents (H + 1) = smithEntropy smithExponents H) := by
  rcases paper_killo_smith_loss_spectrum p n m smithExponents with
    ⟨hcard, hdiff, hmult⟩
  rcases xi_smith_loss_spectrum_plateau_start_total_loss_exists_bound smithExponents with
    ⟨H, hH⟩
  refine ⟨hcard, hdiff, hmult, H, hH, ?_, ?_, ?_⟩
  · intro k hk
    exact smithEntropy_eq_sum_of_all_le smithExponents k fun v hv => le_trans (hH v hv) hk
  · exact smithEntropy_eq_sum_of_all_le smithExponents H hH
  · rw [smithEntropy_eq_sum_of_all_le smithExponents (H + 1)
      (fun v hv => le_trans (hH v hv) (Nat.le_succ H)),
      smithEntropy_eq_sum_of_all_le smithExponents H hH]

end Omega.Zeta
