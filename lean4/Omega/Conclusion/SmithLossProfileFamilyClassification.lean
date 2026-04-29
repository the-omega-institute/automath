import Omega.Conclusion.SmithBoundedRankLossProfileCharacterization

namespace Omega.Conclusion

/-- The pointwise admissibility conditions for one bounded-rank Smith-loss profile. -/
def conclusion_smith_loss_profile_family_classification_admissible
    (m : ℕ) (f : ℕ → ℕ) : Prop :=
  f 0 = 0 ∧
    (∀ k : ℕ, f k ≤ f (k + 1)) ∧
    (∀ k : ℕ, f (k + 2) - f (k + 1) ≤ f (k + 1) - f k) ∧
    (∀ k : ℕ, f (k + 1) - f k ≤ m) ∧
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k → f (k + 1) = f k

/-- The simultaneous realization and atom-recovery statement for a finite family of Smith-loss
profiles indexed by the first `n` local slots. -/
def conclusion_smith_loss_profile_family_classification_statement
    (m n : ℕ) (profile : ℕ → ℕ → ℕ) : Prop :=
  m ≤ n ∧
    (∀ p : Fin n,
      conclusion_smith_bounded_rank_loss_profile_characterization_statement m (profile p)) ∧
    ((∀ p : Fin n,
        conclusion_smith_loss_profile_family_classification_admissible m (profile p)) ↔
      ∃ localSpectrum : Fin n → Multiset ℕ,
        ∀ p : Fin n,
          (∀ k : ℕ, profile p k = Omega.Zeta.smithEntropy (localSpectrum p) k) ∧
            ∀ k : ℕ, Omega.Zeta.smithDelta (localSpectrum p) (k + 1) ≤ m) ∧
    ∀ localSpectrum : Fin n → Multiset ℕ,
      (∀ p : Fin n, ∀ k : ℕ,
        profile p k = Omega.Zeta.smithEntropy (localSpectrum p) k) →
        ∀ (p : Fin n) (t : ℕ),
          ((localSpectrum p).filter fun v => v = t + 1).card =
            (profile p (t + 1) - profile p t) -
              (profile p (t + 2) - profile p (t + 1))

/-- Paper label: `thm:conclusion-smith-loss-profile-family-classification`. -/
theorem paper_conclusion_smith_loss_profile_family_classification
    (m n : Nat) (hmn : m <= n) (profile : Nat -> Nat -> Nat) :
    conclusion_smith_loss_profile_family_classification_statement m n profile := by
  classical
  refine ⟨hmn, ?_, ?_, ?_⟩
  · intro p
    exact conclusion_smith_bounded_rank_loss_profile_characterization_verified m (profile p)
  · constructor
    · intro hadmissible
      have hpoint :
          ∀ p : Fin n, ∃ s : Multiset ℕ,
            (∀ k : ℕ, profile p k = Omega.Zeta.smithEntropy s k) ∧
              ∀ k : ℕ, Omega.Zeta.smithDelta s (k + 1) ≤ m := by
        intro p
        exact
          (conclusion_smith_bounded_rank_loss_profile_characterization_verified
            m (profile p)).1.2 (hadmissible p)
      choose localSpectrum hlocalSpectrum using hpoint
      exact ⟨localSpectrum, hlocalSpectrum⟩
    · rintro ⟨localSpectrum, hlocalSpectrum⟩ p
      exact
        (conclusion_smith_bounded_rank_loss_profile_characterization_verified
          m (profile p)).1.1 ⟨localSpectrum p, hlocalSpectrum p⟩
  · intro localSpectrum hprofile p t
    exact
      (conclusion_smith_bounded_rank_loss_profile_characterization_verified
        m (profile p)).2 (localSpectrum p) (hprofile p) t

end Omega.Conclusion
