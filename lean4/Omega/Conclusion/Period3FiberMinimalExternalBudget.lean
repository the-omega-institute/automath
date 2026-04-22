import Mathlib.Data.Fintype.Card
import Omega.Conclusion.Period3FiberExactMultiplicity

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-period3-fiber-minimal-external-budget`.
The period-`3` fiber is already a Boolean cube on `n` block choices, so any injective binary
residual readout into `B` bits must have room for at least `2 ^ n` states. -/
theorem paper_conclusion_period3_fiber_minimal_external_budget (n B : ℕ)
    (R : Omega.Conclusion.Period3FiberExactMultiplicity.Period3FiberBlockChoices n →
      Fin B → Bool)
    (hR : Function.Injective R) : n ≤ B := by
  have hcard :
      Fintype.card (Omega.Conclusion.Period3FiberExactMultiplicity.Period3FiberBlockChoices n) ≤
        Fintype.card (Fin B → Bool) :=
    Fintype.card_le_of_injective R hR
  have hpow : 2 ^ n ≤ 2 ^ B := by
    simpa [Omega.Conclusion.Period3FiberExactMultiplicity.Period3FiberBlockChoices] using hcard
  exact (Nat.pow_le_pow_iff_right (show 1 < 2 by decide)).1 hpow

end Omega.Conclusion
