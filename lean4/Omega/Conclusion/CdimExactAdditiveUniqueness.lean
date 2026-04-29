import Omega.CircleDimension.CircleDim

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-cdim-exact-additive-uniqueness`. The conclusion-level uniqueness
statement is exactly the axiomatic rigidity theorem for `circleDim`. -/
theorem paper_conclusion_cdim_exact_additive_uniqueness
    (I : Nat → Nat → Nat)
    (hAdd : ∀ a b c d, I (a + b) (c + d) = I a c + I b d)
    (hNorm : I 1 0 = 1) (hFin : ∀ t, I 0 t = 0) :
    ∀ n t, I n t = Omega.CircleDimension.circleDim n t := by
  exact Omega.CircleDimension.circleDim_axiomatic_rigidity I hAdd hNorm hFin

end Omega.Conclusion
