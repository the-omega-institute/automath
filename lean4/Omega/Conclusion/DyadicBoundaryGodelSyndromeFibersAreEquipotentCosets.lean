import Mathlib.Tactic
import Omega.Conclusion.DyadicBoundaryGodelAdmissibleMultiplicativeLinearSubcode

namespace Omega.Conclusion

/-- Paper label:
`thm:conclusion-dyadic-boundary-godel-syndrome-fibers-are-equipotent-cosets`. Every nonempty
syndrome fiber is the translate of the admissible subcode by a chosen basepoint, so its
cardinality agrees with that kernel. -/
theorem paper_conclusion_dyadic_boundary_godel_syndrome_fibers_are_equipotent_cosets
    (m n : Nat) (s : ZMod 2) (x0 : DyadicBoundaryTopChainGroup m n)
    (hx0 : dyadicBoundarySyndrome m n x0 = s) :
    {x : DyadicBoundaryTopChainGroup m n | dyadicBoundarySyndrome m n x = s} =
        {x : DyadicBoundaryTopChainGroup m n |
          ∃ y ∈ dyadicBoundaryAdmissibleSubcode m n, x = x0 + y} ∧
      Fintype.card {x : DyadicBoundaryTopChainGroup m n // dyadicBoundarySyndrome m n x = s} =
        Fintype.card (dyadicBoundaryAdmissibleSubcode m n) := by
  have hs : s = 0 := by
    simpa [dyadicBoundarySyndrome] using hx0.symm
  cases hs
  refine ⟨?_, ?_⟩
  · ext x
    constructor
    · intro _hx
      refine ⟨x - x0, ?_, ?_⟩
      · simp [dyadicBoundaryAdmissibleSubcode, dyadicBoundarySyndrome]
      · calc
          x = (x - x0) + x0 := by simpa using (sub_add_cancel x x0).symm
          _ = x0 + (x - x0) := by rw [add_comm]
    · rintro ⟨y, hy, rfl⟩
      simp [dyadicBoundarySyndrome]
  · have hcardSubcode :
        Fintype.card (dyadicBoundaryAdmissibleSubcode m n) = 2 ^ (2 ^ (m * n)) :=
      (paper_conclusion_dyadic_boundary_godel_admissible_multiplicative_linear_subcode m n).2.2.2
    have hcardFiber :
        Fintype.card {x : DyadicBoundaryTopChainGroup m n // dyadicBoundarySyndrome m n x = 0} =
          2 ^ (2 ^ (m * n)) := by
      simpa [dyadicBoundarySyndrome] using dyadicBoundaryTopChainGroup_card m n
    exact hcardFiber.trans hcardSubcode.symm

end Omega.Conclusion
