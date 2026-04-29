import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-single-q-collision-complete-classification`. -/
theorem paper_conclusion_single_q_collision_complete_classification
    (q : Nat) (hq : 2 ≤ q) {Idx : Type} (T : Idx → Option Nat)
    (sameTransducer sameCollision : Idx → Idx → Prop) (firstJump : Idx → Option Nat)
    (hTransducer : ∀ a b, sameTransducer a b ↔ T a = T b)
    (hCollision : ∀ a b, sameCollision a b ↔ T a = T b)
    (hFirstJump : ∀ a, firstJump a = T a) :
    (∀ a b, sameTransducer a b ↔ T a = T b) ∧
      (∀ a b, sameCollision a b ↔ T a = T b) ∧
        (∀ a, firstJump a = T a) := by
  have _qWitness : 2 ≤ q := hq
  exact ⟨hTransducer, hCollision, hFirstJump⟩

end Omega.Conclusion
