import Mathlib.Data.Multiset.Basic
import Omega.Zeta.XiSmithLossSpectrumDiscreteCurvatureCompleteCharacterization

namespace Omega.Conclusion

/-- Fixed-rank Smith-loss profile statement packaged with the discrete-curvature reconstruction
formula. The rank bound is encoded by the uniform bound on the first differences. -/
def conclusion_smith_bounded_rank_loss_profile_characterization_statement
    (m : ℕ) (f : ℕ → ℕ) : Prop :=
  ((∃ s : Multiset ℕ,
      (∀ k : ℕ, f k = Omega.Zeta.smithEntropy s k) ∧
        ∀ k : ℕ, Omega.Zeta.smithDelta s (k + 1) ≤ m) ↔
    f 0 = 0 ∧
      (∀ k : ℕ, f k ≤ f (k + 1)) ∧
      (∀ k : ℕ, f (k + 2) - f (k + 1) ≤ f (k + 1) - f k) ∧
      (∀ k : ℕ, f (k + 1) - f k ≤ m) ∧
      ∃ N : ℕ, ∀ k : ℕ, N ≤ k → f (k + 1) = f k) ∧
    ∀ s : Multiset ℕ, (∀ k : ℕ, f k = Omega.Zeta.smithEntropy s k) →
      ∀ t : ℕ,
        (s.filter fun v => v = t + 1).card =
          (f (t + 1) - f t) - (f (t + 2) - f (t + 1))

/-- Verification theorem for the bounded-rank Smith-loss profile package. -/
theorem conclusion_smith_bounded_rank_loss_profile_characterization_verified
    (m : ℕ) (f : ℕ → ℕ) :
    conclusion_smith_bounded_rank_loss_profile_characterization_statement m f := by
  refine ⟨?_, ?_⟩
  · constructor
    · rintro ⟨s, hs, hbound⟩
      rcases (Omega.Zeta.paper_xi_smith_padic_loss_spectrum_classification f).1 ⟨s, hs⟩ with
        ⟨h0, hmono, hconc, htail⟩
      refine ⟨h0, hmono, hconc, ?_, htail⟩
      intro k
      have hdelta : f (k + 1) - f k = Omega.Zeta.smithDelta s (k + 1) := by
        rw [hs (k + 1), hs k, Omega.Zeta.smithEntropy_succ_eq_add_delta]
        exact Nat.add_sub_cancel_left _ _
      rw [hdelta]
      exact hbound k
    · rintro ⟨h0, hmono, hconc, hbound, htail⟩
      rcases (Omega.Zeta.paper_xi_smith_padic_loss_spectrum_classification f).2
          ⟨h0, hmono, hconc, htail⟩ with ⟨s, hs⟩
      refine ⟨s, hs, ?_⟩
      intro k
      have hEq : f (k + 1) = f k + Omega.Zeta.smithDelta s (k + 1) := by
        simpa [hs (k + 1), hs k] using Omega.Zeta.smithEntropy_succ_eq_add_delta s k
      have hdelta : f (k + 1) - f k = Omega.Zeta.smithDelta s (k + 1) := by
        rw [hEq, Nat.add_sub_cancel_left]
      rw [← hdelta]
      exact hbound k
  · intro s hs t
    simpa [hs t, hs (t + 1), hs (t + 2)] using
      (Omega.Zeta.paper_xi_smith_loss_discrete_curvature_atoms s).2 t

/-- Paper label: `thm:conclusion-smith-bounded-rank-loss-profile-characterization`. -/
def paper_conclusion_smith_bounded_rank_loss_profile_characterization
    (m : ℕ) (f : ℕ → ℕ) : Prop := by
  exact conclusion_smith_bounded_rank_loss_profile_characterization_statement m f

end Omega.Conclusion
