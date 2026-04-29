import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Omega.GU.SideInformationBitLowerBound

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-joukowsky-discrete-ledger-lower-bound`.
If the Joukowsky branch ambiguity yields an independent sign choice on each of `M` coordinates,
then any injective discrete ledger for those lifts needs at least `2^M` states, hence at least
`M` binary ledger bits. -/
theorem paper_conclusion_joukowsky_discrete_ledger_lower_bound
    (M B : ℕ) (encode : (Fin M → Bool) → Fin B → Bool)
    (hencode : Function.Injective encode) :
    2 ^ M ≤ 2 ^ B ∧ M ≤ B := by
  have hcard :
      Fintype.card (Fin M → Bool) ≤ Fintype.card (Fin B → Bool) :=
    Omega.GU.paper_gut_side_information_bit_lower_bound_package encode hencode
  have hpow : 2 ^ M ≤ 2 ^ B := by
    simpa [Fintype.card_fun, Fintype.card_fin] using hcard
  refine ⟨hpow, ?_⟩
  exact (Nat.pow_le_pow_iff_right (show 1 < 2 by decide)).1 hpow

end Omega.Conclusion
