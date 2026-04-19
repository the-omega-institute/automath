import Mathlib.Tactic

namespace Omega.Conclusion

/-- Idempotent meet semilattices admit no nontrivial additive shadow in `(ℕ^k, +)`.
    thm:conclusion-screen-arithmetic-shadow-additive-linearization-obstruction -/
theorem paper_conclusion_screen_arithmetic_shadow_additive_linearization_obstruction
    {α : Type} {k : ℕ} (meet : α → α → α) (phi : α → Fin k → ℕ) (hidem : ∀ x, meet x x = x)
    (hphi : ∀ x y, phi (meet x y) = fun i => phi x i + phi y i) : ∀ x, phi x = fun _ => 0 := by
  intro x
  have hxx : phi x = fun i => phi x i + phi x i := by
    simpa [hidem x] using hphi x x
  funext i
  have hi : phi x i = phi x i + phi x i := by
    simpa using congrFun hxx i
  omega

end Omega.Conclusion
