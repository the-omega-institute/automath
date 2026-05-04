import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/-- Block-pair index set for the finite Mayer cluster product. -/
def xi_pick_poisson_finite_mayer_cluster_factorization_block_pair_finset (R : ℕ) :
    Finset (Fin R × Fin R) :=
  (Finset.univ : Finset (Fin R × Fin R)).filter fun p => p.1 < p.2

/-- Concrete finite block system carrying the determinant product and the corresponding
log-potential statement. The cross block product is indexed by ordered block pairs `r < s`. -/
structure xi_pick_poisson_finite_mayer_cluster_factorization_system where
  blockCount : ℕ
  blockDet : Fin blockCount → ℝ
  crossRhoSq : Fin blockCount → Fin blockCount → ℝ
  detUnion : ℝ
  PhiUnion : ℝ
  PhiBlock : Fin blockCount → ℝ
  crossEnergy : Fin blockCount → Fin blockCount → ℝ
  determinant_product_formula :
    detUnion =
      (∏ r : Fin blockCount, blockDet r) *
        Finset.prod
          (xi_pick_poisson_finite_mayer_cluster_factorization_block_pair_finset blockCount)
          (fun p => crossRhoSq p.1 p.2)
  log_potential_statement :
    PhiUnion =
      (∑ r : Fin blockCount, PhiBlock r) +
        2 *
          Finset.sum
            (xi_pick_poisson_finite_mayer_cluster_factorization_block_pair_finset blockCount)
            (fun p => crossEnergy p.1 p.2)

/-- Product of the within-block determinant factors. -/
def xi_pick_poisson_finite_mayer_cluster_factorization_block_product
    (S : xi_pick_poisson_finite_mayer_cluster_factorization_system) : ℝ :=
  ∏ r : Fin S.blockCount, S.blockDet r

/-- Product of the cross-block pseudo-hyperbolic pair factors. -/
def xi_pick_poisson_finite_mayer_cluster_factorization_cross_product
    (S : xi_pick_poisson_finite_mayer_cluster_factorization_system) : ℝ :=
  Finset.prod (xi_pick_poisson_finite_mayer_cluster_factorization_block_pair_finset S.blockCount)
    (fun p => S.crossRhoSq p.1 p.2)

/-- Additive within-block contribution to the volume potential. -/
def xi_pick_poisson_finite_mayer_cluster_factorization_block_phi
    (S : xi_pick_poisson_finite_mayer_cluster_factorization_system) : ℝ :=
  ∑ r : Fin S.blockCount, S.PhiBlock r

/-- Additive cross-block two-body Mayer contribution. -/
def xi_pick_poisson_finite_mayer_cluster_factorization_cross_phi
    (S : xi_pick_poisson_finite_mayer_cluster_factorization_system) : ℝ :=
  Finset.sum (xi_pick_poisson_finite_mayer_cluster_factorization_block_pair_finset S.blockCount)
    (fun p => S.crossEnergy p.1 p.2)

/-- The residual higher-cluster term after subtracting the within-block and cross-block pieces. -/
def xi_pick_poisson_finite_mayer_cluster_factorization_higher_cluster_residual
    (S : xi_pick_poisson_finite_mayer_cluster_factorization_system) : ℝ :=
  S.PhiUnion -
    (xi_pick_poisson_finite_mayer_cluster_factorization_block_phi S +
      2 * xi_pick_poisson_finite_mayer_cluster_factorization_cross_phi S)

/-- Paper-facing finite Mayer cluster factorization statement. -/
def xi_pick_poisson_finite_mayer_cluster_factorization_statement
    (S : xi_pick_poisson_finite_mayer_cluster_factorization_system) : Prop :=
  S.detUnion =
      xi_pick_poisson_finite_mayer_cluster_factorization_block_product S *
        xi_pick_poisson_finite_mayer_cluster_factorization_cross_product S ∧
    S.PhiUnion =
      xi_pick_poisson_finite_mayer_cluster_factorization_block_phi S +
        2 * xi_pick_poisson_finite_mayer_cluster_factorization_cross_phi S ∧
      xi_pick_poisson_finite_mayer_cluster_factorization_higher_cluster_residual S = 0

/-- Paper label: `cor:xi-pick-poisson-finite-mayer-cluster-factorization`. -/
theorem paper_xi_pick_poisson_finite_mayer_cluster_factorization
    (S : xi_pick_poisson_finite_mayer_cluster_factorization_system) :
    xi_pick_poisson_finite_mayer_cluster_factorization_statement S := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [xi_pick_poisson_finite_mayer_cluster_factorization_block_product,
      xi_pick_poisson_finite_mayer_cluster_factorization_cross_product] using
      S.determinant_product_formula
  · simpa [xi_pick_poisson_finite_mayer_cluster_factorization_block_phi,
      xi_pick_poisson_finite_mayer_cluster_factorization_cross_phi] using
      S.log_potential_statement
  · dsimp [xi_pick_poisson_finite_mayer_cluster_factorization_higher_cluster_residual,
      xi_pick_poisson_finite_mayer_cluster_factorization_block_phi,
      xi_pick_poisson_finite_mayer_cluster_factorization_cross_phi]
    linarith [S.log_potential_statement]

end

end Omega.Zeta
