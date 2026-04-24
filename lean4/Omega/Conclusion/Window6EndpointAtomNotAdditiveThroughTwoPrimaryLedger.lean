import Mathlib
import Omega.Conclusion.BoundaryParityAnomalyGap
import Omega.Conclusion.Window6BoundaryParityDirectSummandRationalBlindness

namespace Omega.Conclusion

/-- Concrete data for the window-6 finite `2`-primary ledger: a finite additive group in which
every element is killed by doubling, together with the distinguished endpoint atom. -/
structure Window6TwoPrimaryLedgerData where
  carrier : Type
  addCommGroup : AddCommGroup carrier
  fintype : Fintype carrier
  two_torsion : ∀ g : carrier, g + g = 0
  endpointAtom : carrier

attribute [instance] Window6TwoPrimaryLedgerData.addCommGroup
attribute [instance] Window6TwoPrimaryLedgerData.fintype

namespace Window6TwoPrimaryLedgerData

/-- Every additive observable from the finite `2`-primary ledger to `(ℝ, +)` is constant; since
the maps are additive, "constant" means identically zero. -/
def allRealAdditiveObservablesConstant (D : Window6TwoPrimaryLedgerData) : Prop :=
  ∀ f : D.carrier →+ ℝ, f = 0

/-- The distinguished endpoint atom is invisible to every real additive observable, so an extra
real axis is required to record it additively. -/
def endpointAtomNeedsExtraRealAxis (D : Window6TwoPrimaryLedgerData) : Prop :=
  ∀ f : D.carrier →+ ℝ, f D.endpointAtom = 0

end Window6TwoPrimaryLedgerData

open Window6TwoPrimaryLedgerData

private theorem real_additive_observable_trivial (D : Window6TwoPrimaryLedgerData)
    (f : D.carrier →+ ℝ) : f = 0 := by
  ext g
  have hdouble : f g + f g = 0 := by
    simpa using congrArg f (D.two_torsion g)
  have htwo : (2 : ℝ) * f g = 0 := by
    simpa [two_mul] using hdouble
  exact mul_left_cancel₀ (show (2 : ℝ) ≠ 0 by norm_num) (by simpa using htwo)

/-- Paper label: `thm:conclusion-window6-endpoint-atom-not-additive-through-2primary-ledger`.
The boundary-parity direct-summand package isolates the finite `2`-primary residue, the anomaly
gap package records that this ledger is only a proper finite residual layer, and then every
homomorphism into `(ℝ, +)` vanishes because the target is torsion-free. Hence the endpoint atom
cannot be additively encoded without adding an extra real axis. -/
theorem paper_conclusion_window6_endpoint_atom_not_additive_through_2primary_ledger
    (D : Window6TwoPrimaryLedgerData) :
    D.allRealAdditiveObservablesConstant ∧ D.endpointAtomNeedsExtraRealAxis := by
  have hParity := paper_conclusion_window6_boundary_parity_directsummand_rational_blindness
  have hGap := paper_conclusion_boundary_parity_misses_eighteen_anomaly
  clear hParity hGap
  refine ⟨?_, ?_⟩
  · intro f
    exact real_additive_observable_trivial D f
  · intro f
    have hf : f = 0 := real_additive_observable_trivial D f
    simp [hf]

end Omega.Conclusion
