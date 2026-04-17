import Mathlib.Tactic

namespace Omega.Discussion

/-- Equality of determinants is equivalent to the conjunction of trace-sequence equality and
primitive-sequence equality once the Witt-Euler diagram and Möbius invertibility identify the two
paper-facing shadow predicates. -/
theorem paper_discussion_gc_equivalence_characterization
    (detEq traceEq mobEq : Prop) (h1 : detEq ↔ traceEq) (h2 : traceEq ↔ mobEq) :
    detEq ↔ (traceEq ∧ mobEq) := by
  constructor
  · intro hdet
    have htrace : traceEq := h1.mp hdet
    exact ⟨htrace, h2.mp htrace⟩
  · rintro ⟨htrace, _hmob⟩
    exact h1.mpr htrace

end Omega.Discussion
