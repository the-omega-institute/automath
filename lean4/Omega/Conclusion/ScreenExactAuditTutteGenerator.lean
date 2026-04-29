import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-screen-exact-audit-tutte-generator`.

If both the audit coefficient and the Tutte specialization coefficient count the same connected
edge subsets at every redundancy level, then the two coefficient functions agree. -/
theorem paper_conclusion_screen_exact_audit_tutte_generator {E : Type*} [Fintype E]
    [DecidableEq E] (connected : Finset E → Prop) [DecidablePred connected]
    (redundancy : Finset E → ℕ) (auditCoeff tutteCoeff : ℕ → ℕ)
    (hAudit :
      ∀ r,
        auditCoeff r =
          (Finset.univ.filter fun A : Finset E => connected A ∧ redundancy A = r).card)
    (hTutte :
      ∀ r,
        tutteCoeff r =
          (Finset.univ.filter fun A : Finset E => connected A ∧ redundancy A = r).card) :
    auditCoeff = tutteCoeff := by
  funext r
  exact (hAudit r).trans (hTutte r).symm

end Omega.Conclusion
