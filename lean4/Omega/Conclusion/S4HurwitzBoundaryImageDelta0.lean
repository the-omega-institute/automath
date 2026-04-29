import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `prop:conclusion-s4-hurwitz-to-m16-boundary-image-delta0`. -/
theorem paper_conclusion_s4_hurwitz_to_m16_boundary_image_delta0
    {BoundaryComponent ModuliPoint : Type*} (Phi : BoundaryComponent → ModuliPoint)
    (delta : BoundaryComponent → ℕ) (inDelta0 : ModuliPoint → ℕ → Prop)
    (inSeparatingBoundary : ModuliPoint → ℕ → Prop)
    (hdelta : ∀ D, delta D = 12 ∨ delta D = 6 ∨ delta D = 4)
    (himage : ∀ D, inDelta0 (Phi D) (delta D))
    (hsep : ∀ D i, 1 ≤ i → ¬ inSeparatingBoundary (Phi D) i) :
    ∀ D,
      (delta D = 12 ∨ delta D = 6 ∨ delta D = 4) ∧
        inDelta0 (Phi D) (delta D) ∧
          ∀ i, 1 ≤ i → ¬ inSeparatingBoundary (Phi D) i := by
  intro D
  exact ⟨hdelta D, himage D, hsep D⟩

end Omega.Conclusion
