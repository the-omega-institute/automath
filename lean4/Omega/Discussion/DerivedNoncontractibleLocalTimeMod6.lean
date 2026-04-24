import Mathlib.Tactic
import Omega.Conclusion.NoncontractibleLossMod6Explicit

namespace Omega.Discussion

/-- Paper label: `cor:derived-noncontractible-local-time-mod6`.
Rewriting the local-time count by the existing noncontractible-count package and splitting on
`m mod 6` yields the three-phase closed form directly. -/
theorem paper_derived_noncontractible_local_time_mod6 (Tnc : ℕ → ℕ)
    (hT : ∀ m, Tnc m = Omega.Conclusion.noncontractibleFiberCount m) :
    ∀ m, 17 ≤ m →
      Tnc m =
        if m % 6 = 0 ∨ m % 6 = 4 then Omega.Conclusion.noncontractibleMainFiberCount m
        else if m % 6 = 1 ∨ m % 6 = 5 then Omega.Conclusion.noncontractibleSecondFiberCount m
        else Omega.Conclusion.noncontractibleThirdFiberCount m := by
  intro m _hm
  rw [hT m]
  have hmlt : m % 6 < 6 := Nat.mod_lt _ (by omega)
  interval_cases hm6 : m % 6 <;>
    simp [Omega.Conclusion.noncontractibleFiberCount, hm6]

end Omega.Discussion
