import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Conclusion

/-- Paper label: `prop:conclusion-window6-ramanujan-blind-residual-channel`. -/
theorem paper_conclusion_window6_ramanujan_blind_residual_channel :
    let eps : Fin 21 → Int :=
      fun r =>
        if (r : Nat) = 0 then 0
        else if (r : Nat) ≤ 8 then 1
        else if (r : Nat) ≤ 12 then 0
        else -1
    let c : Nat → Fin 21 → Int :=
      fun q r =>
        if q = 1 then 1
        else if q = 3 then
          if (r : Nat) % 3 = 0 then 2 else -1
        else if q = 7 then
          if (r : Nat) % 7 = 0 then 6 else -1
        else if q = 21 then
          if (r : Nat) = 0 then 12
          else if (r : Nat) % 3 = 0 then -2
          else if (r : Nat) % 7 = 0 then -6
          else 1
        else 0
    eps 0 = 0 ∧
      (∀ r : Fin 21, 1 ≤ (r : Nat) → (r : Nat) ≤ 8 → eps r = 1) ∧
      (∀ r : Fin 21, 9 ≤ (r : Nat) → (r : Nat) ≤ 12 → eps r = 0) ∧
      (∀ r : Fin 21, 13 ≤ (r : Nat) → eps r = -1) ∧
      (∑ r : Fin 21, eps r * c 1 r = 0) ∧
      (∑ r : Fin 21, eps r * c 3 r = 0) ∧
      (∑ r : Fin 21, eps r * c 7 r = 0) ∧
      (∑ r : Fin 21, eps r * c 21 r = 0) ∧
      (∑ r : Fin 21, eps r * eps r = 16) := by
  native_decide

end Omega.Conclusion
