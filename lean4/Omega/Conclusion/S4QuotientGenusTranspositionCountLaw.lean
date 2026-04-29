import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete Riemann--Hurwitz ledger for the `S₄` quotient genus transposition-count law. -/
structure conclusion_s4_quotient_genus_transposition_count_law_data where
  subgroupOrder : ℚ
  subgroupOrder_ne_zero : subgroupOrder ≠ 0
  transpositionCount : ℚ
  quotientGenus : ℚ
  genusX : ℚ
  fixedPointsPerTransposition : ℚ
  totalRamification : ℚ
  genusX_eq : genusX = 49
  fixedPointsPerTransposition_eq : fixedPointsPerTransposition = 24
  totalRamification_eq : totalRamification = fixedPointsPerTransposition * transpositionCount
  riemannHurwitz :
    2 * genusX - 2 = subgroupOrder * (2 * quotientGenus - 2) + totalRamification

/-- The quotient map is etale exactly when its ramification ledger is zero. -/
def conclusion_s4_quotient_genus_transposition_count_law_etale
    (D : conclusion_s4_quotient_genus_transposition_count_law_data) : Prop :=
  D.totalRamification = 0

/-- Paper-facing statement of the genus formula and the etale criterion. -/
def conclusion_s4_quotient_genus_transposition_count_law_statement
    (D : conclusion_s4_quotient_genus_transposition_count_law_data) : Prop :=
  D.quotientGenus = 1 + (48 - 12 * D.transpositionCount) / D.subgroupOrder ∧
    (conclusion_s4_quotient_genus_transposition_count_law_etale D ↔
      D.transpositionCount = 0)

/-- Paper label: `thm:conclusion-s4-quotient-genus-transposition-count-law`. -/
theorem paper_conclusion_s4_quotient_genus_transposition_count_law
    (D : conclusion_s4_quotient_genus_transposition_count_law_data) :
    conclusion_s4_quotient_genus_transposition_count_law_statement D := by
  have hRH := D.riemannHurwitz
  rw [D.genusX_eq, D.totalRamification_eq, D.fixedPointsPerTransposition_eq] at hRH
  have hnum : D.subgroupOrder * (D.quotientGenus - 1) =
      48 - 12 * D.transpositionCount := by
    nlinarith
  constructor
  · have hdiv :
        (48 - 12 * D.transpositionCount) / D.subgroupOrder = D.quotientGenus - 1 := by
      rw [← hnum]
      field_simp [D.subgroupOrder_ne_zero]
    calc
      D.quotientGenus = 1 + (D.quotientGenus - 1) := by ring
      _ = 1 + (48 - 12 * D.transpositionCount) / D.subgroupOrder := by rw [hdiv]
  · constructor
    · intro hetale
      have hram :
          24 * D.transpositionCount = 0 := by
        simpa [conclusion_s4_quotient_genus_transposition_count_law_etale,
          D.totalRamification_eq, D.fixedPointsPerTransposition_eq] using hetale
      nlinarith
    · intro hzero
      simp [conclusion_s4_quotient_genus_transposition_count_law_etale,
        D.totalRamification_eq, D.fixedPointsPerTransposition_eq, hzero]

end Omega.Conclusion
