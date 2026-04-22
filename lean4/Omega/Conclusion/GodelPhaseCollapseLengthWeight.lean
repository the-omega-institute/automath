import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic
import Omega.Conclusion.PrimeShiftPhaseVisibleTwoGenerator

namespace Omega.Conclusion

open Omega.GroupUnification

/-- Paper-facing formulation of the phase-collapse principle: once the Gödel lift records only the
visible pair `(length, total code weight)`, every additive phase readout is constant on words with
the same two scalars. -/
def conclusion_godel_phase_collapse_length_weight_statement {α : Type*} (code : α → ℕ)
    (lift : List α → PrimeShiftLedger)
    (_hlift : ∀ w, primeShiftPi (lift w) = (w.length, (w.map code).sum)) : Prop :=
  (∀ w, primeShiftPi (lift w) = (w.length, (w.map code).sum)) ∧
    ∀ {B : Type*} [AddCommGroup B] (f : PrimeShiftLedger → B),
      f (0, 0) = 0 →
      (∀ x y, f (primeShiftMul x y) = f x + f y) →
      ∀ {w w' : List α},
        w.length = w'.length →
        (w.map code).sum = (w'.map code).sum →
        f (lift w) = f (lift w')

/-- Paper label: `cor:conclusion-godel-phase-collapse-length-weight`. Any additive phase readout on
the prime-shift ledger factors through the visible quotient `(length, total code weight)`, so equal
length and equal total code weight force identical readouts after the Gödel lift. -/
theorem paper_conclusion_godel_phase_collapse_length_weight {α A : Type*} [AddCommGroup A]
    (code : α → ℕ) (lift : List α → PrimeShiftLedger)
    (hlift : ∀ w, primeShiftPi (lift w) = (w.length, (w.map code).sum)) :
    conclusion_godel_phase_collapse_length_weight_statement code lift hlift := by
  refine ⟨hlift, ?_⟩
  intro B _ f hzero hmul w w' hlen hsum
  rcases paper_conclusion_prime_shift_phase_visible_two_generator f hzero hmul with
    ⟨g, hg, _⟩
  have hpi : primeShiftPi (lift w) = primeShiftPi (lift w') := by
    rw [hlift w, hlift w', hlen, hsum]
  have hgpi : g (primeShiftPi (lift w)) = g (primeShiftPi (lift w')) := congrArg g hpi
  simpa [hg.2 (lift w), hg.2 (lift w')] using hgpi

end Omega.Conclusion
