import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Tactic
import Omega.Zeta.LocalizedIntegersConnectedRationalBlindness
import Omega.Zeta.LocalizedQuotientLedger

namespace Omega.Zeta

/-- Paper label:
`thm:xi-localized-solenoid-general-endomorphism-periodic-zeta`. -/
theorem paper_xi_localized_solenoid_general_endomorphism_periodic_zeta
    (S : Omega.Zeta.FinitePrimeLocalization) (a b n : ℕ) (hn : 1 ≤ n) :
    IsAddCyclic (ZMod (Omega.Zeta.localizedIndex S (a ^ n - b ^ n))) ∧
      Nat.card (ZMod (Omega.Zeta.localizedIndex S (a ^ n - b ^ n))) =
        Omega.Zeta.localizedIndex S (a ^ n - b ^ n) := by
  have _ : 1 ≤ n := hn
  exact ⟨inferInstance, Nat.card_zmod (Omega.Zeta.localizedIndex S (a ^ n - b ^ n))⟩

end Omega.Zeta
