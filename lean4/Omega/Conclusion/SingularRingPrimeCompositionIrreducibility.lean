import Mathlib.Tactic
import Omega.Conclusion.SingularRingFaithfulSemigroup

namespace Omega.Conclusion

theorem paper_conclusion_singular_ring_prime_composition_irreducibility
    (D : Omega.Conclusion.SingularRingFaithfulSemigroupData) (n : ℕ) (hn : 2 ≤ n) :
    Nat.Prime n ↔
      ¬ ∃ a b : ℕ, 2 ≤ a ∧ 2 ≤ b ∧
        Function.comp (D.rationalMap a) (D.rationalMap b) = D.rationalMap n := by
  rcases paper_conclusion_singular_ring_faithful_semigroup D with ⟨hsemigroup, hfaithful⟩
  constructor
  · intro hprime hdecomp
    rcases hdecomp with ⟨a, b, ha, hb, hcomp⟩
    have hab_eq : a * b = n := by
      have hmaps : D.rationalMap (a * b) = D.rationalMap n := by
        exact (hsemigroup a b (by omega) (by omega)).symm.trans hcomp
      exact (hfaithful (a * b) n hmaps).2
    exact (Nat.not_prime_of_mul_eq hab_eq (by omega) (by omega)) hprime
  · intro hindecomp
    rw [Nat.prime_def_lt']
    refine ⟨hn, ?_⟩
    intro a ha hlt hdiv
    rcases hdiv with ⟨b, rfl⟩
    have hb0 : b ≠ 0 := by
      intro hb0
      subst hb0
      simp at hlt
    have hb1 : b ≠ 1 := by
      intro hb1
      subst hb1
      simp at hlt
    have hb : 2 ≤ b := by
      have hb_pos : 0 < b := Nat.pos_of_ne_zero hb0
      have hb_one_lt : 1 < b := lt_of_le_of_ne (Nat.succ_le_of_lt hb_pos) hb1.symm
      exact Nat.succ_le_of_lt hb_one_lt
    apply hindecomp
    refine ⟨a, b, ha, hb, ?_⟩
    simpa using hsemigroup a b (by omega) (by omega)

end Omega.Conclusion
