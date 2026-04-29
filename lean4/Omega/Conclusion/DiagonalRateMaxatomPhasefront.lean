import Mathlib.Tactic

namespace Omega.Conclusion

noncomputable section

/-- Concrete data for the diagonal-rate phase front with fixed maximal atom mass. -/
structure conclusion_diagonal_rate_maxatom_phasefront_Data where
  maxAtom : ℝ

namespace conclusion_diagonal_rate_maxatom_phasefront_Data

/-- The quadratic phase-front defect at maximal atom mass `m`. -/
def deltaC (_D : conclusion_diagonal_rate_maxatom_phasefront_Data) (m : ℝ) : ℝ :=
  m * (1 - m)

/-- The phase-front statement: the quadratic has vertex `1/2`, value `1/4`, and no larger value. -/
def phasefront_statement (D : conclusion_diagonal_rate_maxatom_phasefront_Data) : Prop :=
  deltaC D D.maxAtom = D.maxAtom * (1 - D.maxAtom) ∧
    (∀ m : ℝ, deltaC D m = 1 / 4 - (m - 1 / 2) ^ 2) ∧
      (∀ m : ℝ, deltaC D m ≤ 1 / 4) ∧
        (∀ m : ℝ, deltaC D m = 1 / 4 → m = 1 / 2)

end conclusion_diagonal_rate_maxatom_phasefront_Data

/-- Paper label: `thm:conclusion-diagonal-rate-maxatom-phasefront`. -/
theorem paper_conclusion_diagonal_rate_maxatom_phasefront
    (D : conclusion_diagonal_rate_maxatom_phasefront_Data) :
    D.phasefront_statement := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro m
    unfold conclusion_diagonal_rate_maxatom_phasefront_Data.deltaC
    ring
  · intro m
    have hsquare : 0 ≤ (m - 1 / 2) ^ 2 := sq_nonneg (m - 1 / 2)
    have hvertex :
        conclusion_diagonal_rate_maxatom_phasefront_Data.deltaC D m =
          1 / 4 - (m - 1 / 2) ^ 2 := by
      unfold conclusion_diagonal_rate_maxatom_phasefront_Data.deltaC
      ring
    rw [hvertex]
    nlinarith
  · intro m hmax
    have hvertex :
        conclusion_diagonal_rate_maxatom_phasefront_Data.deltaC D m =
          1 / 4 - (m - 1 / 2) ^ 2 := by
      unfold conclusion_diagonal_rate_maxatom_phasefront_Data.deltaC
      ring
    rw [hvertex] at hmax
    have hsquare_zero : (m - 1 / 2) ^ 2 = 0 := by nlinarith
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsquare_zero)

end

end Omega.Conclusion
