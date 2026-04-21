import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper-facing wrapper: the stable addition law is exactly successor-translation, and the same
operation agrees with the fold-based addition interface.
    cor:conclusion-stable-successor-translation-addition -/
theorem paper_conclusion_stable_successor_translation_addition {X : Type*} (S : X → X)
    (Val : X → Nat) (add foldAdd : X → X → X)
    (hSucc : ∀ c d, add c d = Nat.iterate S (Val d) c)
    (hFold : ∀ c d, add c d = foldAdd c d) :
    ∀ c d, add c d = Nat.iterate S (Val d) c ∧ add c d = foldAdd c d := by
  intro c d
  exact ⟨hSucc c d, hFold c d⟩

end Omega.Conclusion
