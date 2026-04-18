import Mathlib.Tactic

namespace Omega.POM

/-- If equivalence in a fixed-temperature soft fragment were expressive enough to preserve the
hard first-fit semantic equivalence via a compiler, then decidability of the soft relation would
transfer back to the hard relation, contradicting the assumed undecidability.
    thm:pom-soft-order-fixed-temp-nondefinability -/
theorem paper_pom_soft_order_fixed_temp_nondefinability {Hard Soft : Type*}
    (hardEq : Hard → Hard → Prop) (softEq : Soft → Soft → Prop)
    (hSoftDecidable : Nonempty (∀ u v, Decidable (softEq u v)))
    (hHardUndecidable : ¬ Nonempty (∀ w₁ w₂, Decidable (hardEq w₁ w₂))) :
    ¬ ∃ compile : Hard → Soft,
        ∀ w₁ w₂, hardEq w₁ w₂ ↔ softEq (compile w₁) (compile w₂) := by
  intro hCompile
  rcases hCompile with ⟨compile, hCompile⟩
  rcases hSoftDecidable with ⟨hSoftDecidable⟩
  apply hHardUndecidable
  refine ⟨?_⟩
  intro w₁ w₂
  letI := hSoftDecidable (compile w₁) (compile w₂)
  exact decidable_of_iff (softEq (compile w₁) (compile w₂)) (hCompile w₁ w₂).symm

end Omega.POM
