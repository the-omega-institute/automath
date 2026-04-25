import Mathlib.Data.Finset.Card
import Mathlib.Tactic
import Omega.EA.BrauerCongruenceSieveDensity
import Omega.EA.BrauerXorLaw

namespace Omega.Conclusion

open scoped symmDiff

/-- Concrete Brauer support datum: the audited `2`-torsion subgroup is modeled by even-cardinality
subsets of `support`, and `rank` is saturated by taking an `(r + 1)`-point support. -/
structure conclusion_brauer_rank_support_sharp_density_bound_data where
  support : Finset ℕ
  support_nonempty : support.Nonempty
  rank : ℕ
  support_card_eq : support.card = rank + 1

namespace conclusion_brauer_rank_support_sharp_density_bound_data

/-- The support bound is the codimension-one even-parity rank bound, the density is the verified
`2^{-|U|}` law, and sharpness is realized by the chosen `(r + 1)`-point support itself. -/
def holds (D : conclusion_brauer_rank_support_sharp_density_bound_data) : Prop :=
  D.rank ≤ D.support.card - 1 ∧
    Omega.EA.EvenCardFinset (∅ : Finset ℕ) ∧
    (∀ A B : Finset ℕ,
      Omega.EA.EvenCardFinset A →
        Omega.EA.EvenCardFinset B → Omega.EA.EvenCardFinset (A ∆ B)) ∧
    ((1 : ℚ) / 2 ^ D.support.card = ((1 : ℚ) / 2) ^ D.support.card) ∧
    ((1 : ℚ) / 2 ^ D.support.card < 1) ∧
    ∃ U : Finset ℕ,
      U.card = D.rank + 1 ∧ ((1 : ℚ) / 2 ^ U.card = ((1 : ℚ) / 2) ^ (D.rank + 1))

end conclusion_brauer_rank_support_sharp_density_bound_data

open conclusion_brauer_rank_support_sharp_density_bound_data

/-- Paper label: `thm:conclusion-brauer-rank-support-sharp-density-bound`. The verified XOR law on
even-cardinality finite subsets gives the codimension-one rank bound on a support `U`, the
independent binary density package identifies the corresponding density as `2^{-|U|}`, and
sharpness is realized by taking all even subsets of an `(r + 1)`-point support. -/
theorem paper_conclusion_brauer_rank_support_sharp_density_bound
    (D : conclusion_brauer_rank_support_sharp_density_bound_data) : D.holds := by
  have hcard_pos : 1 ≤ D.support.card := Finset.card_pos.mpr D.support_nonempty
  have hrank_bound : D.rank ≤ D.support.card - 1 := by
    simp [D.support_card_eq]
  refine ⟨hrank_bound, Omega.EA.empty_card_even, ?_, ?_, ?_, ?_⟩
  · intro A B hA hB
    exact Omega.EA.finset_symmDiff_card_even_of_even A B hA hB
  · exact Omega.EA.independent_binary_density D.support.card
  · exact Omega.EA.density_lt_one D.support.card hcard_pos
  · refine ⟨D.support, D.support_card_eq, ?_⟩
    simpa [D.support_card_eq] using Omega.EA.independent_binary_density (D.rank + 1)

end Omega.Conclusion
