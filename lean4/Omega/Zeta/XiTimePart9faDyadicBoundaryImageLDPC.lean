import Mathlib.Tactic
import Omega.SPG.DyadicBoundaryImageMinDistance

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part9fa-dyadic-boundary-image-ldpc`. -/
theorem paper_xi_time_part9fa_dyadic_boundary_image_ldpc
    {Cn Cn1 : Type*} [AddGroup Cn] [AddGroup Cn1]
    (boundaryTop : Cn → Cn1) (n m : ℕ) (hn : 1 ≤ n)
    (hSub : ∀ u v, boundaryTop (u - v) = boundaryTop u - boundaryTop v)
    (hKer : ∀ u, boundaryTop u = 0 → u = 0) :
    (let code := Omega.SPG.dyadicBoundaryImageCode boundaryTop
     Omega.SPG.dyadicBoundaryImageBlockLength n m = n * (2 ^ m + 1) * 2 ^ ((n - 1) * m) ∧
      Omega.SPG.dyadicBoundaryImageDimension boundaryTop n m = 2 ^ (n * m) ∧
      Omega.SPG.dyadicBoundaryImageRate n m = (2 ^ m : ℚ) / (n * (2 ^ m + 1)) ∧
      Omega.SPG.dyadicBoundaryImageMinDistance m n = 2 * n ∧
      Omega.SPG.dyadicBoundaryCheckDegree = 4 ∧
      Omega.SPG.dyadicBoundaryVariableDegree n = 2 * (n - 1) ∧
      code = Set.range boundaryTop) := by
  have hldpc :=
    Omega.SPG.paper_spg_dyadic_boundary_image_ldpc boundaryTop n m hSub hKer
  have hdist := Omega.SPG.paper_spg_dyadic_boundary_image_min_distance m n hn
  dsimp at hldpc ⊢
  rcases hldpc with ⟨hblock, hdim, hrate, hcheck, hvar, hcode⟩
  exact ⟨hblock, hdim, hrate, hdist, hcheck, hvar, hcode⟩

end Omega.Zeta
