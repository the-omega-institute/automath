import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-fold-audit-nonminimal-idempotent-pointwise-kl-witness`. -/
theorem paper_conclusion_fold_audit_nonminimal_idempotent_pointwise_kl_witness
    {Micro Macro : Type}
    (Dmicro : Micro → Micro → Real)
    (Dmacro : Macro → Macro → Real)
    (P : Micro → Macro)
    (Q : Macro → Micro)
    (κ : Macro → Macro)
    (hPQ : ∀ ν, P (Q ν) = ν)
    (hDself : ∀ μ, Dmicro μ μ = 0)
    (hstrict : ∀ ν, κ ν ≠ ν → 0 < Dmacro ν (κ ν))
    (hdecomp :
      ∀ μ,
        Dmicro μ (Q (κ (P μ))) =
          Dmacro (P μ) (κ (P μ)) + Dmicro μ (Q (P μ)))
    (ν : Macro)
    (hν : κ ν ≠ ν) :
    ∃ μ,
      Dmicro μ (Q (κ (P μ))) > Dmicro μ (Q (P μ)) ∧
        Dmicro μ (Q (P μ)) = 0 := by
  refine ⟨Q ν, ?_, ?_⟩
  · rw [hdecomp (Q ν), hPQ ν]
    linarith [hstrict ν hν, hDself (Q ν)]
  · simpa [hPQ ν] using hDself (Q ν)

end Omega.Conclusion
