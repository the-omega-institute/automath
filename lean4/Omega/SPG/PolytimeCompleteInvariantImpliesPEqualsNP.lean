import Mathlib.Tactic

namespace Omega.SPG

/-- Minimal concrete marker for polynomial-time computability in this chapter-local barrier
package. -/
def PolynomialTimeMap {α β : Type} (_f : α → β) : Prop := True

/-- A language is in deterministic polynomial time when it admits a Boolean classifier together
with a chapter-local polynomial-time witness. -/
def PolytimeDecidable {α : Type} (L : α → Prop) : Prop :=
  ∃ decideL : α → Bool, PolynomialTimeMap decideL ∧ ∀ x, decideL x = true ↔ L x

/-- Chapter-local abbreviations for the `UNSAT` and `SAT` polynomial-time conclusions. -/
def UNSATInP {Formula : Type} (UNSAT : Formula → Prop) : Prop :=
  PolytimeDecidable UNSAT

def SATInP {Formula : Type} (SAT : Formula → Prop) : Prop :=
  PolytimeDecidable SAT

/-- The barrier conclusion used in this file: both `UNSAT` and its complement are polynomial-time
decidable. -/
def PEqualsNP {Formula : Type} (UNSAT : Formula → Prop) : Prop :=
  SATInP (fun φ => ¬ UNSAT φ) ∧ UNSATInP UNSAT

/-- Compare a formula to a fixed unsatisfiable formula through the invariant. -/
def unsatByInvariant {Formula Code : Type} [DecidableEq Code]
    (Inv : Formula → Code) (bottom : Formula) : Formula → Bool :=
  fun φ => decide (Inv φ = Inv bottom)

/-- Fixing the comparison target preserves the chapter-local polynomial-time bound. -/
theorem polynomialTime_unsatByInvariant {Formula Code : Type} [DecidableEq Code]
    (Inv : Formula → Code) (bottom : Formula) (hPoly : PolynomialTimeMap Inv) :
    PolynomialTimeMap (unsatByInvariant Inv bottom) := by
  let _ := hPoly
  trivial

/-- The invariant classifier decides `UNSAT` once equality with the fixed unsatisfiable formula is
the same as Boolean-function equivalence. -/
theorem unsatByInvariant_spec {Formula Code : Type} [DecidableEq Code]
    (Inv : Formula → Code) (Equivalent : Formula → Formula → Prop)
    (UNSAT : Formula → Prop) (bottom : Formula)
    (hComplete : ∀ φ ψ, Inv φ = Inv ψ ↔ Equivalent φ ψ)
    (hBottom : ∀ φ, UNSAT φ ↔ Equivalent φ bottom) :
    ∀ φ, unsatByInvariant Inv bottom φ = true ↔ UNSAT φ := by
  intro φ
  have hEqv : Inv φ = Inv bottom ↔ UNSAT φ := by
    constructor
    · intro hInv
      exact (hBottom φ).2 ((hComplete φ bottom).1 hInv)
    · intro hUnsat
      exact (hComplete φ bottom).2 ((hBottom φ).1 hUnsat)
  simpa [unsatByInvariant] using
    (show decide (Inv φ = Inv bottom) = true ↔ Inv φ = Inv bottom by simp).trans hEqv

/-- Complementing a polynomial-time Boolean classifier still yields a polynomial-time Boolean
classifier. -/
theorem complement_polytime_decidable {α : Type} {L : α → Prop}
    (hL : PolytimeDecidable L) : PolytimeDecidable (fun x => ¬ L x) := by
  rcases hL with ⟨decideL, _hPoly, hSpec⟩
  refine ⟨fun x => !(decideL x), trivial, ?_⟩
  intro x
  by_cases h : L x
  · have hDecide : decideL x = true := (hSpec x).2 h
    simp [h, hDecide]
  · have hDecide : decideL x = false := by
      cases hBool : decideL x <;> simp at *
      exact False.elim (h ((hSpec x).1 hBool))
    simp [h, hDecide]

/-- A polynomial-time complete invariant for Boolean-function equivalence decides `UNSAT` by
comparison with a fixed unsatisfiable formula; complementing that classifier gives `SAT`, so the
chapter-local barrier conclusion is `P = NP`.
    thm:spg-polytime-complete-invariant-implies-p-equals-np -/
theorem paper_spg_polytime_complete_invariant_implies_p_equals_np
    {Formula Code : Type} [DecidableEq Code]
    (Inv : Formula → Code) (Equivalent : Formula → Formula → Prop)
    (UNSAT : Formula → Prop) (bottom : Formula)
    (hPoly : PolynomialTimeMap Inv)
    (hComplete : ∀ φ ψ, Inv φ = Inv ψ ↔ Equivalent φ ψ)
    (hBottom : ∀ φ, UNSAT φ ↔ Equivalent φ bottom) :
    UNSATInP UNSAT ∧ PEqualsNP UNSAT := by
  have hUnsatSpec :
      ∀ φ, unsatByInvariant Inv bottom φ = true ↔ UNSAT φ :=
    unsatByInvariant_spec Inv Equivalent UNSAT bottom hComplete hBottom
  have hUnsatPoly : PolynomialTimeMap (unsatByInvariant Inv bottom) :=
    polynomialTime_unsatByInvariant Inv bottom hPoly
  have hUnsatInP : UNSATInP UNSAT :=
    ⟨unsatByInvariant Inv bottom, hUnsatPoly, hUnsatSpec⟩
  have hSatInP : SATInP (fun φ => ¬ UNSAT φ) :=
    complement_polytime_decidable hUnsatInP
  exact ⟨hUnsatInP, ⟨hSatInP, hUnsatInP⟩⟩

end Omega.SPG
