import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete contradiction package for uniaxial universality versus a faithful high-rank
`p`-adic hidden readout. -/
structure conclusion_uniaxial_prime_register_universality_incompatible_high_rank_faithfulness_data where
  pcdim : ℕ
  hiddenRank : ℕ
  uniaxialUniversality_pcdim :
    pcdim = 1
  faithfulHiddenReadout_lowerBound :
    hiddenRank ≤ pcdim
  highRank :
    2 ≤ hiddenRank

namespace conclusion_uniaxial_prime_register_universality_incompatible_high_rank_faithfulness_data

/-- The advertised incompatibility is the impossibility of satisfying all three concrete bounds. -/
def conclusion_uniaxial_prime_register_universality_incompatible_high_rank_faithfulness_clauses
    (D :
      conclusion_uniaxial_prime_register_universality_incompatible_high_rank_faithfulness_data) :
    Prop :=
  ¬ (D.pcdim = 1 ∧ D.hiddenRank ≤ D.pcdim ∧ 2 ≤ D.hiddenRank)

end conclusion_uniaxial_prime_register_universality_incompatible_high_rank_faithfulness_data

/-- Root-level paper statement name used by the target theorem. -/
def conclusion_uniaxial_prime_register_universality_incompatible_high_rank_faithfulness_statement
    (D :
      conclusion_uniaxial_prime_register_universality_incompatible_high_rank_faithfulness_data) :
    Prop :=
  D.conclusion_uniaxial_prime_register_universality_incompatible_high_rank_faithfulness_clauses

/-- Paper label:
`thm:conclusion-uniaxial-prime-register-universality-incompatible-high-rank-faithfulness`. -/
theorem paper_conclusion_uniaxial_prime_register_universality_incompatible_high_rank_faithfulness
    (D :
      conclusion_uniaxial_prime_register_universality_incompatible_high_rank_faithfulness_data) :
    conclusion_uniaxial_prime_register_universality_incompatible_high_rank_faithfulness_statement
      D := by
  have hle_one : D.hiddenRank ≤ 1 := by
    simpa [D.uniaxialUniversality_pcdim] using D.faithfulHiddenReadout_lowerBound
  have hcontr : False := by
    exact not_lt_of_ge D.highRank (Nat.lt_of_le_of_lt hle_one (by norm_num))
  intro _
  exact hcontr

end Omega.Conclusion
