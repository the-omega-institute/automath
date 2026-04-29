import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part9g-affine-semigroup-unique-fixed-point`. -/
theorem paper_xi_time_part9g_affine_semigroup_unique_fixed_point {T R : Type}
    [AddGroup T] [Zero R] (B : ℕ → T → T) (ev : R → T) (sub inv : ℕ → T → T)
    (hSub : ∀ k x b, sub k x = b ↔ x = B k x + b)
    (hLeft : ∀ k b, 1 ≤ k → sub k (inv k b) = b)
    (hRight : ∀ k x, 1 ≤ k → inv k (sub k x) = x)
    (hFaithful : ∀ r, ev r = 0 → r = 0) (hev0 : ev 0 = 0) :
    (∀ r k, 1 ≤ k → ∃! x, x = B k x + ev r) ∧
      (∀ r, (∃ x, x = x + ev r) ↔ r = 0) := by
  constructor
  · intro r k hk
    refine ⟨inv k (ev r), ?_, ?_⟩
    · exact (hSub k (inv k (ev r)) (ev r)).mp (hLeft k (ev r) hk)
    · intro y hy
      have hSubY : sub k y = ev r := (hSub k y (ev r)).mpr hy
      calc
        y = inv k (sub k y) := (hRight k y hk).symm
        _ = inv k (ev r) := by rw [hSubY]
  · intro r
    constructor
    · rintro ⟨x, hx⟩
      apply hFaithful
      have hCancel : x + 0 = x + ev r := by simpa using hx
      exact (add_left_cancel hCancel).symm
    · intro hr
      subst hr
      exact ⟨0, by simp [hev0]⟩

end Omega.Zeta
