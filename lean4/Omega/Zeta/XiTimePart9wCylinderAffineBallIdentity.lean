import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-time-part9w-cylinder-affine-ball-identity`. -/
theorem paper_xi_time_part9w_cylinder_affine_ball_identity {Seq T : Type} [AddCommGroup T]
    (X : Seq → T) (cylinder : List ℕ → Set Seq) (ball : List ℕ → Set T)
    (hmem : ∀ a e, e ∈ cylinder a ↔ X e ∈ ball a ∩ Set.range X) :
    ∀ a, X '' cylinder a = ball a ∩ Set.range X := by
  intro a
  ext t
  constructor
  · intro ht
    rcases ht with ⟨e, he, rfl⟩
    exact (hmem a e).1 he
  · intro ht
    rcases ht.2 with ⟨e, rfl⟩
    exact ⟨e, (hmem a e).2 ht, rfl⟩

end Omega.Zeta
