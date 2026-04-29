import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete visible-channel quotient data for the anomaly/winding obstruction.
The integer winding descends from visible channels to the strictification quotient. -/
structure xi_anom_winding_obstruction_data where
  Channel : Type
  Quotient : Type
  quotient : Channel → Quotient
  lift : Quotient → Channel
  lift_quotient : ∀ q : Quotient, quotient (lift q) = q
  normalizedWinding : Channel → ℤ
  quotientWinding : Quotient → ℤ
  winding_descends : ∀ c : Channel, normalizedWinding c = quotientWinding (quotient c)

/-- All visible channels have normalized zero winding. -/
def xi_anom_winding_obstruction_visible_zero (D : xi_anom_winding_obstruction_data) : Prop :=
  ∀ c : D.Channel, D.normalizedWinding c = 0

/-- The quotient winding is identically zero on the BC strictification quotient. -/
def xi_anom_winding_obstruction_quotient_zero (D : xi_anom_winding_obstruction_data) : Prop :=
  ∀ q : D.Quotient, D.quotientWinding q = 0

/-- The normalized visible winding factors through the strictification quotient. -/
def xi_anom_winding_obstruction_factorization (D : xi_anom_winding_obstruction_data) :
    Prop :=
  ∃ quotientWinding' : D.Quotient → ℤ,
    D.normalizedWinding = fun c : D.Channel => quotientWinding' (D.quotient c)

/-- Paper-facing iff statement: visible zero winding is equivalent to zero winding
on the quotient together with the universal factorization through that quotient. -/
def xi_anom_winding_obstruction_data.statement (D : xi_anom_winding_obstruction_data) :
    Prop :=
  xi_anom_winding_obstruction_visible_zero D ↔
    xi_anom_winding_obstruction_quotient_zero D ∧
      xi_anom_winding_obstruction_factorization D

/-- thm:xi-anom-winding-obstruction -/
theorem paper_xi_anom_winding_obstruction (D : xi_anom_winding_obstruction_data) :
    D.statement := by
  constructor
  · intro hvisible
    refine ⟨?_, ?_⟩
    · intro q
      calc
        D.quotientWinding q = D.quotientWinding (D.quotient (D.lift q)) := by
          rw [D.lift_quotient q]
        _ = D.normalizedWinding (D.lift q) := (D.winding_descends (D.lift q)).symm
        _ = 0 := hvisible (D.lift q)
    · refine ⟨D.quotientWinding, ?_⟩
      funext c
      exact D.winding_descends c
  · intro hquot c
    exact (D.winding_descends c).trans (hquot.1 (D.quotient c))

end Omega.Zeta
