import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-unique-global-shortest-history-ray`. -/
theorem paper_conclusion_unique_global_shortest_history_ray (Good : (Nat → Nat) → Prop)
    (hone : Good (fun _ => 1))
    (hprefix : ∀ a : Nat → Nat, Good a → ∀ T i : Nat, i < T → a i = 1) :
    ∃! a : Nat → Nat, Good a := by
  refine ⟨fun _ => 1, hone, ?_⟩
  intro a ha
  funext i
  exact hprefix a ha (i + 1) i (Nat.lt_succ_self i)

end Omega.Conclusion
