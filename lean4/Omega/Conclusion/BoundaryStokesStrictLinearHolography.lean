import Mathlib
import Omega.SPG.DyadicFiniteMomentCompleteness

namespace Omega.Conclusion

/-- Fixed-resolution boundary-image coordinates for the top-dimensional dyadic chain model. -/
abbrev BoundaryImageIndex (m n : ℕ) := Fin (2 ^ (m * n))

/-- Fixed-resolution tensor-moment coordinates. -/
abbrev BoundaryMomentIndex (m n : ℕ) := Fin (2 ^ (m * n))

/-- Top-chain coefficient space in the dyadic boundary/Stokes package. -/
abbrev BoundaryChainSpace (m n : ℕ) := BoundaryImageIndex m n → ℚ

/-- Boundary-image coefficient space. -/
abbrev BoundaryImageSpace (m n : ℕ) := BoundaryImageIndex m n → ℚ

/-- Complete tensor-moment box. -/
abbrev BoundaryMomentBoxSpace (m n : ℕ) := BoundaryMomentIndex m n → ℚ

/-- In the paper-facing model, the top boundary map identifies the boundary image with the
top-chain coordinates, so its inverse is the identity linear equivalence. -/
noncomputable def boundaryMapInverse (m n : ℕ) :
    BoundaryImageSpace m n ≃ₗ[ℚ] BoundaryChainSpace m n :=
  LinearEquiv.refl ℚ _

private theorem dyadicMomentBox_bijective (m n : ℕ) :
    Function.Bijective (Omega.SPG.dyadicMomentBox (m := m) (n := n)) := by
  refine ⟨Omega.SPG.paper_spg_dyadic_finite_moment_completeness (m := m) (n := n), ?_⟩
  intro α
  exact ⟨α, rfl⟩

/-- Linear version of the dyadic finite-moment completeness theorem on the coordinate box. -/
noncomputable def dyadicFiniteMomentCompletenessLinearEquiv (m n : ℕ) :
    BoundaryChainSpace m n ≃ₗ[ℚ] BoundaryMomentBoxSpace m n :=
  LinearEquiv.funCongrLeft ℚ ℚ
    (Equiv.ofBijective (Omega.SPG.dyadicMomentBox (m := m) (n := n))
      (dyadicMomentBox_bijective m n)).symm

/-- Boundary Stokes holography is the complete moment box transported along the inverse of the
top boundary map. -/
noncomputable def boundaryStokesStrictLinearHolography (m n : ℕ) :
    BoundaryImageSpace m n ≃ₗ[ℚ] BoundaryMomentBoxSpace m n :=
  (boundaryMapInverse m n).trans (dyadicFiniteMomentCompletenessLinearEquiv m n)

/-- Paper label: `thm:conclusion-boundary-stokes-strict-linear-holography`. -/
theorem paper_conclusion_boundary_stokes_strict_linear_holography (m n : ℕ) :
    (boundaryStokesStrictLinearHolography m n).toLinearMap =
        (dyadicFiniteMomentCompletenessLinearEquiv m n).toLinearMap.comp
          (boundaryMapInverse m n).toLinearMap ∧
      Function.Bijective (boundaryStokesStrictLinearHolography m n) := by
  constructor
  · rfl
  · simpa using (boundaryStokesStrictLinearHolography m n).bijective

end Omega.Conclusion
