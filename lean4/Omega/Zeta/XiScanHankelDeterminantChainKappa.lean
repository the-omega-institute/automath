import Omega.Zeta.XiComovingScanHankelRankDefect

namespace Omega.Zeta

open Matrix
open scoped BigOperators

/-- Concrete determinant-chain package for the finite atomic scan Hankel block at length `κ`. -/
def xi_scan_hankel_determinant_chain_kappa_statement
    (κ : Nat) (D : XiFiniteAtomicMomentData κ) : Prop :=
  D.hankelDetFactorsAsVandermondeSquare ∧
    ∀ (_hweights : ∀ j : Fin κ, D.weights j ≠ 0) (_hnodes : Function.Injective D.nodes),
      D.hankel.det = (∏ j, D.weights j) * (Matrix.vandermonde D.nodes).det ^ 2 ∧
        D.hankel.det ≠ 0 ∧ D.hankel.rank = κ

/-- Paper label: `prop:xi-scan-hankel-determinant-chain-kappa`. The finite atomic
Hankel--Vandermonde factorization supplies the determinant chain, and nonzero weights together
with distinct nodes force the terminal Hankel block to be nonsingular and full rank. -/
theorem paper_xi_scan_hankel_determinant_chain_kappa (κ : Nat)
    (D : XiFiniteAtomicMomentData κ) :
    xi_scan_hankel_determinant_chain_kappa_statement κ D := by
  refine ⟨paper_xi_depth_hankel_determinant_vandermonde_square κ D, ?_⟩
  intro hweights hnodes
  have hscan := paper_xi_comoving_scan_hankel_rank_defect κ D hweights hnodes
  have hweight_prod_ne : (∏ j : Fin κ, D.weights j) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr fun j _ => hweights j
  have hvandermonde_det_ne : (Matrix.vandermonde D.nodes).det ≠ 0 := by
    exact Matrix.det_vandermonde_ne_zero_iff.mpr hnodes
  have hhankel_det_ne : D.hankel.det ≠ 0 := by
    rw [hscan.1.2]
    exact mul_ne_zero hweight_prod_ne (pow_ne_zero 2 hvandermonde_det_ne)
  exact ⟨hscan.1.2, hhankel_det_ne, hscan.2⟩

end Omega.Zeta
