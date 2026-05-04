import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part9q-patterson-sullivan-boundary-dimension`. -/
theorem paper_xi_time_part9q_patterson_sullivan_boundary_dimension
    (Boundary : Type*) (a lambda : ℝ) (exactDim fullSupport ahlforsRegular : Prop)
    (localDim hausdorffDim : Boundary → ℝ) (hExact : exactDim)
    (hLocal : ∀ ξ : Boundary, localDim ξ = lambda / a)
    (hAhlfors : fullSupport → ahlforsRegular)
    (hHaus : ahlforsRegular → ∀ ξ : Boundary, hausdorffDim ξ = lambda / a) :
    exactDim ∧ (∀ ξ : Boundary, localDim ξ = lambda / a) ∧
      (fullSupport → ahlforsRegular ∧ ∀ ξ : Boundary, hausdorffDim ξ = lambda / a) := by
  exact ⟨hExact, hLocal, fun hFull => ⟨hAhlfors hFull, hHaus (hAhlfors hFull)⟩⟩

end Omega.Zeta
