import Omega.Conclusion.BinfoldMellinEscortSemigroup
import Omega.Conclusion.TwoAtomScalarRecoveryAlpha2

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-binfold-two-constant-completeness`. The single two-atom scalar
recovers the golden parameter on `(1, ∞)`, the circle constant is fixed independently, and the
golden Mellin/escort tower then transports to the recovered parameter. -/
theorem paper_conclusion_binfold_two_constant_completeness (α φ c : ℝ) (hα : 1 < α)
    (hφ : 1 < φ) (hScalar : twoAtomScalar α φ = twoAtomScalar α Real.goldenRatio)
    (hCircle : c = 2 * Real.pi) :
    φ = Real.goldenRatio ∧ c = 2 * Real.pi ∧ BinfoldMellinEscortSemigroup φ := by
  have hφ_eq : φ = Real.goldenRatio := by
    exact (twoAtomScalar_injective_on_Ioi hα) hφ Real.one_lt_goldenRatio hScalar
  refine ⟨hφ_eq, hCircle, ?_⟩
  simpa [hφ_eq] using paper_conclusion_binfold_mellin_escort_semigroup

end Omega.Conclusion
