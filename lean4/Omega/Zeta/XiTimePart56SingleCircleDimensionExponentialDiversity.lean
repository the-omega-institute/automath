import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-time-part56-single-circle-dimension-exponential-diversity`. -/
theorem paper_xi_time_part56_single_circle_dimension_exponential_diversity
    (n : ℕ) (_hn : 1 ≤ n) (SigmaFamily : Finset (Fin n) → Type*)
    (sameCircleQuotient : Finset (Fin n) → Prop) (hSame : ∀ E, sameCircleQuotient E)
    (hRigid : ∀ E F, Nonempty (SigmaFamily E ≃ SigmaFamily F) → E = F) :
    ∃ I : Finset (Finset (Fin n)),
      I.card = 2 ^ n ∧
        (∀ E ∈ I, sameCircleQuotient E) ∧
          ∀ E ∈ I, ∀ F ∈ I, Nonempty (SigmaFamily E ≃ SigmaFamily F) → E = F := by
  refine ⟨Finset.univ, ?_, ?_, ?_⟩
  · simp
  · intro E hE
    exact hSame E
  · intro E hE F hF hEquiv
    exact hRigid E F hEquiv

end Omega.Zeta
