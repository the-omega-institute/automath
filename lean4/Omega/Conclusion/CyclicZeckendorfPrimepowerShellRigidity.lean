import Omega.Conclusion.CyclicZeckendorfPrimeRegularBias

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-cyclic-zeckendorf-primepower-shell-rigidity`. This wrapper
packages the sector closed form for the shell representatives `0, p^0, …, p^(ν-1)` together
with the prime-level regular-bias formula used to calibrate the `ν = 1` case. -/
theorem paper_conclusion_cyclic_zeckendorf_primepower_shell_rigidity (p ν : ℕ) (hp : p.Prime) :
    cyclicZeckendorfCharacterMultiplicity (p ^ ν) 0 =
      cyclicZeckendorfCharacterClosedForm (p ^ ν) 0 ∧
    (∀ t, t < ν →
      cyclicZeckendorfCharacterMultiplicity (p ^ ν) (p ^ t) =
        cyclicZeckendorfCharacterClosedForm (p ^ ν) (p ^ t)) ∧
    let a_p : ℤ := (cyclicZeckendorfLucas p - 1) / p
    cyclicZeckendorfCharacterMultiplicity p 0 = a_p + 1 ∧
      (∀ k, 0 < k → k < p → cyclicZeckendorfCharacterMultiplicity p k = a_p) := by
  refine ⟨?_, ?_, ?_⟩
  · exact (paper_conclusion_cyclic_zeckendorf_sector_character_closed_form (p ^ ν) 0).2.2.2
  · intro t ht
    exact (paper_conclusion_cyclic_zeckendorf_sector_character_closed_form (p ^ ν) (p ^ t)).2.2.2
  · simpa using paper_conclusion_cyclic_zeckendorf_prime_regular_bias p hp

end Omega.Conclusion
