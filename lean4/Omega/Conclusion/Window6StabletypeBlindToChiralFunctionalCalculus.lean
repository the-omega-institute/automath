import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label:
`thm:conclusion-window6-stabletype-blind-to-chiral-functional-calculus`.
Stable-type observables are orthogonal to every chiral-minus vector reached by the
abstract polynomial functional calculi for `A` and `Delta`. -/
theorem paper_conclusion_window6_stabletype_blind_to_chiral_functional_calculus
    {V Poly : Type} (Stable ChiralMinus : V → Prop) (orthogonal : V → V → Prop)
    (eval : Poly → (V → V) → V → V) (A Delta : V → V)
    (hStableOrth : ∀ g f, Stable g → ChiralMinus f → orthogonal g f)
    (hEvalA : ∀ P f, ChiralMinus f → ChiralMinus (eval P A f))
    (hEvalDelta : ∀ P f, ChiralMinus f → ChiralMinus (eval P Delta f)) (P : Poly)
    {g f : V} (hg : Stable g) (hf : ChiralMinus f) :
    orthogonal g (eval P A f) ∧ orthogonal g (eval P Delta f) := by
  exact ⟨hStableOrth g (eval P A f) hg (hEvalA P f hf),
    hStableOrth g (eval P Delta f) hg (hEvalDelta P f hf)⟩

end Omega.Conclusion
