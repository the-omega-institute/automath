import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-torus-extension-pontryagin-classification`. -/
theorem paper_conclusion_torus_extension_pontryagin_classification
    (compactConnectedExtensions dualTorsionFreeEmbeddings : Type*)
    (toDual : compactConnectedExtensions → dualTorsionFreeEmbeddings)
    (toCompact : dualTorsionFreeEmbeddings → compactConnectedExtensions)
    (left_inv : ∀ E, toCompact (toDual E) = E)
    (right_inv : ∀ D, toDual (toCompact D) = D) :
    Nonempty (compactConnectedExtensions ≃ dualTorsionFreeEmbeddings) := by
  exact ⟨
    { toFun := toDual
      invFun := toCompact
      left_inv := left_inv
      right_inv := right_inv }⟩

end Omega.Conclusion
