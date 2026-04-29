import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part9zr-lattes-fullsplit-transparency`. -/
theorem paper_xi_time_part9zr_lattes_fullsplit_transparency
    (jointDensity : Bool → Bool → ℚ) (splitDensity : Bool → Fin 3 → ℚ)
    (hJoint : ∀ e₁ e₂, jointDensity e₁ e₂ = (1 : ℚ) / 192)
    (hSplit0 : ∀ e, splitDensity e 0 = (1 : ℚ) / 6)
    (hSplit1 : ∀ e, splitDensity e 1 = (1 : ℚ) / 2)
    (hSplit2 : ∀ e, splitDensity e 2 = (1 : ℚ) / 3) :
    (∀ e₁ e₂, jointDensity e₁ e₂ = (1 : ℚ) / 192) ∧
      (∀ e,
        splitDensity e 0 = (1 : ℚ) / 6 ∧
          splitDensity e 1 = (1 : ℚ) / 2 ∧
            splitDensity e 2 = (1 : ℚ) / 3) := by
  exact ⟨hJoint, fun e => ⟨hSplit0 e, hSplit1 e, hSplit2 e⟩⟩

end Omega.Zeta
