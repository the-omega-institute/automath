import Omega.Conclusion.MixedHiddenStateFiniteTruncationHomCount
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped Classical

/-- The finite hidden-state receiver used for prime-support visibility. -/
abbrev conclusion_mixed_hiddenstate_prime_support_complete_splitting_receiver
    (beta N : ℕ) : Type :=
  conclusion_mixed_hiddenstate_finite_truncation_hom_count_receiver beta N

/-- Prime visibility for the mixed hidden-state finite observer: the binary hidden sector
sees `2`, while the cyclic truncation sees precisely the prime divisors of `N`. -/
def conclusion_mixed_hiddenstate_prime_support_complete_splitting_visible
    (N p : ℕ) : Prop :=
  p = 2 ∨ p ∣ N

/-- The product factors exposed by the finite-truncation hom-count package. -/
def conclusion_mixed_hiddenstate_prime_support_complete_splitting_visible_factors
    (beta N : ℕ) (G : Type*) [AddMonoid G] : Type _ :=
  (Fin beta → conclusion_mixed_hiddenstate_finite_truncation_hom_count_torsion G 2) ×
    conclusion_mixed_hiddenstate_finite_truncation_hom_count_torsion G N

/-- Paper-facing statement for the prime-support complete splitting. -/
def conclusion_mixed_hiddenstate_prime_support_complete_splitting_statement : Prop :=
  ∀ beta N : ℕ,
    ∀ G : Type*, ∀ [AddCommMonoid G], ∀ [Fintype G],
      Nonempty
          (conclusion_mixed_hiddenstate_finite_truncation_hom_count_hom_data beta N G ≃
            conclusion_mixed_hiddenstate_prime_support_complete_splitting_visible_factors
              beta N G) ∧
        Fintype.card
            (conclusion_mixed_hiddenstate_finite_truncation_hom_count_hom_data beta N G) =
          Fintype.card
              (conclusion_mixed_hiddenstate_finite_truncation_hom_count_torsion G 2) ^ beta *
            Fintype.card
              (conclusion_mixed_hiddenstate_finite_truncation_hom_count_torsion G N) ∧
        ∀ p : ℕ,
          Nat.Prime p →
            ¬ conclusion_mixed_hiddenstate_prime_support_complete_splitting_visible N p →
              ¬ p ∣ 2 * N

/-- Paper label: `thm:conclusion-mixed-hiddenstate-prime-support-complete-splitting`. -/
theorem paper_conclusion_mixed_hiddenstate_prime_support_complete_splitting :
    conclusion_mixed_hiddenstate_prime_support_complete_splitting_statement := by
  intro beta N G _ _
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨conclusion_mixed_hiddenstate_finite_truncation_hom_count_hom_split beta N G⟩
  · exact
      (paper_conclusion_mixed_hiddenstate_finite_truncation_hom_count beta N G).2
  · intro p hp hnot hdiv
    have hvisible : conclusion_mixed_hiddenstate_prime_support_complete_splitting_visible N p := by
      rcases hp.dvd_mul.mp hdiv with hp2 | hpN
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hp2)
      · exact Or.inr hpN
    exact hnot hvisible

end Omega.Conclusion
