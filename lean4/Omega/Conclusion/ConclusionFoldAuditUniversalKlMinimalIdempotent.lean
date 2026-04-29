import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-fold-audit-universal-kl-minimal-idempotent`. -/
theorem paper_conclusion_fold_audit_universal_kl_minimal_idempotent
    {Micro Macro : Type}
    (Dmicro : Micro → Micro → Real)
    (Dmacro : Macro → Macro → Real)
    (P : Micro → Macro)
    (Q : Macro → Micro)
    (κ : Macro → Macro)
    (K w : Micro → Micro)
    (hK : ∀ μ, K μ = Q (P μ))
    (hw : ∀ μ, w μ = Q (κ (P μ)))
    (hdecomp :
      ∀ μ, Dmicro μ (w μ) = Dmacro (P μ) (κ (P μ)) + Dmicro μ (K μ))
    (hnonneg : ∀ ν, 0 ≤ Dmacro ν (κ ν)) :
    ∀ μ, Dmicro μ (w μ) ≥ Dmicro μ (K μ) := by
  intro μ
  have hμ := hdecomp μ
  rw [hw μ, hK μ] at hμ ⊢
  rw [hμ]
  linarith [hnonneg (P μ)]

end Omega.Conclusion
