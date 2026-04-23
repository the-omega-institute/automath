import Mathlib.LinearAlgebra.Matrix.Rank
import Omega.Zeta.XiDepthHankelDeterminantVandermondeSquare

namespace Omega.Zeta

open Matrix

/-- Paper label: `thm:xi-comoving-scan-hankel-rank-defect`. For a finite exponential sample
profile `uₙ = Σⱼ Aⱼ zⱼⁿ`, the verified Hankel--Vandermonde factorization identifies the square
Hankel block with a Vandermonde Gram matrix; distinct nodes make the Vandermonde determinant
nonzero, hence the block has full rank `κ`. -/
theorem paper_xi_comoving_scan_hankel_rank_defect
    (κ : Nat) (D : XiFiniteAtomicMomentData κ)
    (hweights : ∀ j : Fin κ, D.weights j ≠ 0) (hnodes : Function.Injective D.nodes) :
    D.hankelDetFactorsAsVandermondeSquare ∧ D.hankel.rank = κ := by
  have hfactor := paper_xi_depth_hankel_determinant_vandermonde_square κ D
  have hweight_prod_ne :
      (∏ j : Fin κ, D.weights j) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr fun j _ => hweights j
  have hvandermonde_det_ne : (Matrix.vandermonde D.nodes).det ≠ 0 := by
    exact Matrix.det_vandermonde_ne_zero_iff.mpr hnodes
  have hhankel_det_ne : D.hankel.det ≠ 0 := by
    rw [hfactor.2]
    exact mul_ne_zero hweight_prod_ne (pow_ne_zero 2 hvandermonde_det_ne)
  have hhankel_unit : IsUnit D.hankel := by
    exact
      (Matrix.isUnit_iff_isUnit_det (A := D.hankel)).2
        (isUnit_iff_ne_zero.mpr hhankel_det_ne)
  exact ⟨hfactor, by simpa using Matrix.rank_of_isUnit D.hankel hhankel_unit⟩

end Omega.Zeta
