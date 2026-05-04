import Mathlib.Tactic

namespace Omega.Conclusion

/-- A concrete sector-polynomial invariant: its length spectrum is the data retained by the
geometric holographic coordinate. -/
structure conclusion_sector_polynomial_vs_toggle_algebra_holography_collapse_splitting_sectorPolynomial where
  conclusion_sector_polynomial_vs_toggle_algebra_holography_collapse_splitting_lengths :
    List ℕ

/-- The abstract toggle algebra remembers only the number of Boolean sectors. -/
structure conclusion_sector_polynomial_vs_toggle_algebra_holography_collapse_splitting_toggleAlgebra where
  conclusion_sector_polynomial_vs_toggle_algebra_holography_collapse_splitting_booleanSectorCount :
    ℕ

namespace conclusion_sector_polynomial_vs_toggle_algebra_holography_collapse_splitting_sectorPolynomial

/-- Number of Cartesian prime factors visible to the Boolean sector algebra. -/
def conclusion_sector_polynomial_vs_toggle_algebra_holography_collapse_splitting_rank
    (P :
      conclusion_sector_polynomial_vs_toggle_algebra_holography_collapse_splitting_sectorPolynomial) :
    ℕ :=
  P.conclusion_sector_polynomial_vs_toggle_algebra_holography_collapse_splitting_lengths.length

/-- Boolean sector count extracted from the sector-polynomial side. -/
def conclusion_sector_polynomial_vs_toggle_algebra_holography_collapse_splitting_booleanSectorCount
    (P :
      conclusion_sector_polynomial_vs_toggle_algebra_holography_collapse_splitting_sectorPolynomial) :
    ℕ :=
  2 ^
    P.conclusion_sector_polynomial_vs_toggle_algebra_holography_collapse_splitting_rank

/-- Forget the length spectrum and retain the abstract Boolean toggle algebra. -/
def conclusion_sector_polynomial_vs_toggle_algebra_holography_collapse_splitting_forget
    (P :
      conclusion_sector_polynomial_vs_toggle_algebra_holography_collapse_splitting_sectorPolynomial) :
    conclusion_sector_polynomial_vs_toggle_algebra_holography_collapse_splitting_toggleAlgebra where
  conclusion_sector_polynomial_vs_toggle_algebra_holography_collapse_splitting_booleanSectorCount :=
    P.conclusion_sector_polynomial_vs_toggle_algebra_holography_collapse_splitting_booleanSectorCount

end conclusion_sector_polynomial_vs_toggle_algebra_holography_collapse_splitting_sectorPolynomial

open conclusion_sector_polynomial_vs_toggle_algebra_holography_collapse_splitting_sectorPolynomial

/-- Concrete content of the holography/collapse split: the forgetful map preserves the Boolean
sector count, identifies any two sector-polynomial invariants with the same length-spectrum
cardinality, and is strict because different length spectra can have the same Boolean count. -/
def conclusion_sector_polynomial_vs_toggle_algebra_holography_collapse_splitting_statement :
    Prop :=
  (∀ P :
      conclusion_sector_polynomial_vs_toggle_algebra_holography_collapse_splitting_sectorPolynomial,
      (P.conclusion_sector_polynomial_vs_toggle_algebra_holography_collapse_splitting_forget).conclusion_sector_polynomial_vs_toggle_algebra_holography_collapse_splitting_booleanSectorCount =
        P.conclusion_sector_polynomial_vs_toggle_algebra_holography_collapse_splitting_booleanSectorCount) ∧
    (∀ P Q :
      conclusion_sector_polynomial_vs_toggle_algebra_holography_collapse_splitting_sectorPolynomial,
      P.conclusion_sector_polynomial_vs_toggle_algebra_holography_collapse_splitting_rank =
          Q.conclusion_sector_polynomial_vs_toggle_algebra_holography_collapse_splitting_rank →
        P.conclusion_sector_polynomial_vs_toggle_algebra_holography_collapse_splitting_forget =
          Q.conclusion_sector_polynomial_vs_toggle_algebra_holography_collapse_splitting_forget) ∧
      ∃ P Q :
        conclusion_sector_polynomial_vs_toggle_algebra_holography_collapse_splitting_sectorPolynomial,
        P.conclusion_sector_polynomial_vs_toggle_algebra_holography_collapse_splitting_forget =
            Q.conclusion_sector_polynomial_vs_toggle_algebra_holography_collapse_splitting_forget ∧
          P.conclusion_sector_polynomial_vs_toggle_algebra_holography_collapse_splitting_lengths ≠
            Q.conclusion_sector_polynomial_vs_toggle_algebra_holography_collapse_splitting_lengths

/-- Paper label:
`thm:conclusion-sector-polynomial-vs-toggle-algebra-holography-collapse-splitting`. -/
theorem paper_conclusion_sector_polynomial_vs_toggle_algebra_holography_collapse_splitting :
    conclusion_sector_polynomial_vs_toggle_algebra_holography_collapse_splitting_statement := by
  refine ⟨?_, ?_, ?_⟩
  · intro P
    rfl
  · intro P Q hRank
    simp [
      conclusion_sector_polynomial_vs_toggle_algebra_holography_collapse_splitting_forget,
      conclusion_sector_polynomial_vs_toggle_algebra_holography_collapse_splitting_booleanSectorCount,
      hRank]
  · refine ⟨
      { conclusion_sector_polynomial_vs_toggle_algebra_holography_collapse_splitting_lengths := [0] },
      { conclusion_sector_polynomial_vs_toggle_algebra_holography_collapse_splitting_lengths := [1] },
      ?_, ?_⟩
    · rfl
    · intro h
      norm_num at h

end Omega.Conclusion
