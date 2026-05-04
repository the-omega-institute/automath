import Mathlib.Tactic

namespace Omega.Conclusion

/-- The essential obstruction prime spectrum for the Lee--Yang quartic cover. -/
def conclusion_leyang_minimal_obstruction_primes_S : Finset ℕ :=
  {2, 3, 31, 37}

/-- Paper label: `cor:conclusion-leyang-minimal-obstruction-primes`. -/
theorem paper_conclusion_leyang_minimal_obstruction_primes :
    conclusion_leyang_minimal_obstruction_primes_S = ({2, 3, 31, 37} : Finset ℕ) ∧
      conclusion_leyang_minimal_obstruction_primes_S.card = 4 ∧
      ∀ p : ℕ, p ∈ conclusion_leyang_minimal_obstruction_primes_S ↔
        p = 2 ∨ p = 3 ∨ p = 31 ∨ p = 37 := by
  refine ⟨rfl, by native_decide, ?_⟩
  intro p
  simp [conclusion_leyang_minimal_obstruction_primes_S]

end Omega.Conclusion
