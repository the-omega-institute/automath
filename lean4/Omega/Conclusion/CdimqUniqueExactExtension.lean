import Omega.CircleDimension.CircleDim

namespace Omega.Conclusion

/-- Paper-facing uniqueness wrapper for the exact additive extension of circle dimension. -/
theorem paper_conclusion_cdimq_unique_exact_extension (δ : Nat → Nat → Nat)
    (hTors : ∀ t : Nat, δ 0 t = 0)
    (hAdd : ∀ a b c d : Nat, δ (a + b) (c + d) = δ a c + δ b d)
    (hNorm : δ 1 0 = 1) :
    ∀ r t : Nat, δ r t = Omega.CircleDimension.circleDim r t := by
  exact Omega.CircleDimension.circleDim_axiomatic_rigidity δ hAdd hNorm hTors

end Omega.Conclusion
