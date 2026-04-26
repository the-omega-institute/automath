import Mathlib.Tactic
import Omega.Conclusion.LmaxPrimeProgrammability

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-lmax-not-finite-primeizable`. -/
theorem paper_conclusion_lmax_not_finite_primeizable (S : Finset Nat)
    (hDir : ∃ p : Nat, Nat.Prime p ∧ p % 3 = 2 ∧ 5 ≤ p ∧ p ∉ S) :
    ∃ P : Finset Nat,
      (∀ p ∈ P, Nat.Prime p ∧ p % 3 = 2 ∧ 5 ≤ p) ∧
        (∃ p ∈ P, p ∉ S) ∧
          conclusion_lmax_prime_programmability_orbit_length P = P.prod id := by
  rcases hDir with ⟨p, hp_prime, hp_mod, hp_ge, hp_not_mem⟩
  refine ⟨{p}, ?_, ?_, ?_⟩
  · intro q hq
    rw [Finset.mem_singleton] at hq
    subst q
    exact ⟨hp_prime, hp_mod, hp_ge⟩
  · exact ⟨p, by simp, hp_not_mem⟩
  · apply paper_conclusion_lmax_prime_programmability
    intro q hq
    rw [Finset.mem_singleton] at hq
    subst q
    exact ⟨hp_prime, hp_mod, hp_ge⟩

end Omega.Conclusion
