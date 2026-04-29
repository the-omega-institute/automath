import Omega.Zeta.SmithPrefixSufficiency

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-smith-minimal-solenoidal-host-by-bad-primes`. -/
theorem paper_conclusion_smith_minimal_solenoidal_host_by_bad_primes {m : ℕ}
    (E : ℕ → Fin m → ℕ) (S : Finset ℕ)
    (hS : ∀ p, p ∈ S ↔ ∃ i : Fin m, 0 < E p i) :
    (∀ p, p ∉ S → Omega.Zeta.smithPrefixTop (E p) = 0) ∧
      ∀ T : Finset ℕ,
        ((∀ p ∈ S, p ∈ T) ↔ ∀ p i, 0 < E p i → p ∈ T) := by
  constructor
  · intro p hp_not_mem
    have hp_no_exp : ¬ ∃ i : Fin m, 0 < E p i := by
      intro hp_exp
      exact hp_not_mem ((hS p).2 hp_exp)
    apply le_antisymm
    · unfold Omega.Zeta.smithPrefixTop
      refine Finset.sup_le ?_
      intro i _
      have hi_not_pos : ¬ 0 < E p i := by
        intro hi_pos
        exact hp_no_exp ⟨i, hi_pos⟩
      omega
    · exact Nat.zero_le _
  · intro T
    constructor
    · intro hST p i hE
      exact hST p ((hS p).2 ⟨i, hE⟩)
    · intro hT p hpS
      rcases (hS p).1 hpS with ⟨i, hi⟩
      exact hT p i hi

end Omega.Conclusion
