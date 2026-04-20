import Mathlib.Tactic
import Omega.CircleDimension.CircleDim

namespace Omega.Conclusion

open Omega.CircleDimension

/-- Conclusion-level wrapper: circle dimension is the free rank, and in the bookkeeping model it
is additive across short exact sequences.
    thm:conclusion-cdim-rank-and-short-exact-additivity -/
theorem paper_conclusion_cdim_rank_and_short_exact_additivity
    (rA rB rC tA tB tC : Nat) (hshort : rB = rA + rC) :
    circleDim rB tB = rB ∧ circleDim rB tB = circleDim rA tA + circleDim rC tC := by
  have hrank : circleDim rB tB = rB := by
    simp [circleDim]
  have hadd : circleDim rB tB = circleDim rA tA + circleDim rC tC := by
    rw [hshort]
    calc
      circleDim (rA + rC) tB = circleDim (rA + rC) (tA + tC) :=
        circleDim_finite_extension (rA + rC) tB (tA + tC)
      _ = circleDim rA tA + circleDim rC tC := circleDim_add rA rC tA tC
  exact ⟨hrank, hadd⟩

end Omega.Conclusion
