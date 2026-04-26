import Omega.Folding.MaxFiberTwoStep

namespace Omega.POM

/-- Paper label: `prop:pom-hidden-bit-first-non10-gate`. -/
theorem paper_pom_hidden_bit_first_non10_gate (m : Nat) (w : Omega.Word (m + 3)) :
    (w ⟨m + 2, by omega⟩ = false → Omega.hiddenBit w = 0) ∧
      (w ⟨m + 2, by omega⟩ = true →
        Omega.hiddenBit w =
          if w ⟨m + 1, by omega⟩ = true then 1
          else Omega.hiddenBit (Omega.truncate (Omega.truncate w))) := by
  constructor
  · intro hLast
    exact Omega.hiddenBit_last_false (m := m + 2) w hLast
  · intro hLast
    exact Omega.hiddenBit_unified_recurrence (m := m) w hLast

end Omega.POM
