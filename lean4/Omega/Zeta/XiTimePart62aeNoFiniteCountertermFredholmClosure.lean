import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-time-part62ae-no-finite-counterterm-fredholm-closure`. -/
theorem paper_xi_time_part62ae_no_finite_counterterm_fredholm_closure {Op : Type*}
    (R : Op) (sub add : Op → Op → Op) (FiniteRank TraceClass HilbertSchmidt : Op → Prop)
    (hTraceHS : ∀ A, TraceClass A → HilbertSchmidt A)
    (hFiniteHS : ∀ F, FiniteRank F → HilbertSchmidt F)
    (hAddHS : ∀ A B, HilbertSchmidt A → HilbertSchmidt B → HilbertSchmidt (add A B))
    (hSubCancel : ∀ F, add (sub R F) F = R) (hRnotHS : ¬ HilbertSchmidt R) :
    ¬ ∃ F, FiniteRank F ∧ TraceClass (sub R F) := by
  rintro ⟨F, hFinite, hTraceSub⟩
  exact hRnotHS ((hSubCancel F) ▸ hAddHS (sub R F) F (hTraceHS (sub R F) hTraceSub)
    (hFiniteHS F hFinite))

end Omega.Zeta
