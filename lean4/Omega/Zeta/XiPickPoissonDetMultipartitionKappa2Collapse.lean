import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Zeta

/-- Cross-block representatives for a multipartition: each unordered block pair appears once. -/
def xi_pick_poisson_det_multipartition_kappa2_collapse_blockPairs
    (blockCount : ℕ) : Finset (Fin blockCount × Fin blockCount) :=
  (Finset.univ.product (Finset.univ : Finset (Fin blockCount))).filter
    (fun pair => pair.1 < pair.2)

/-- Concrete multipartition data for the Pick--Poisson determinant collapse.  The block-internal
factor is separated from the cross-block product over ordered representatives `i < j`; uniform
separation then bounds each cross-block contribution by `rho0 ^ 2`. -/
structure xi_pick_poisson_det_multipartition_kappa2_collapse_data where
  blockCount : ℕ
  internalFactor : Fin blockCount → ℝ
  crossFactor : Fin blockCount → Fin blockCount → ℝ
  rho0 : ℝ
  detP : ℝ
  hcrossFactor_nonneg : ∀ i j, 0 ≤ crossFactor i j
  hcrossFactor_le : ∀ i j, i < j → crossFactor i j ≤ rho0 ^ 2
  hdetP :
    detP =
      (∏ i, internalFactor i) *
        ∏ pair ∈ xi_pick_poisson_det_multipartition_kappa2_collapse_blockPairs blockCount,
          crossFactor pair.1 pair.2

namespace xi_pick_poisson_det_multipartition_kappa2_collapse_data

/-- The block-internal determinant contribution. -/
def blockInternalProduct
    (D : xi_pick_poisson_det_multipartition_kappa2_collapse_data) : ℝ :=
  ∏ i, D.internalFactor i

/-- The product of all cross-block Pick--Poisson factors. -/
def crossBlockProduct
    (D : xi_pick_poisson_det_multipartition_kappa2_collapse_data) : ℝ :=
  ∏ pair ∈ xi_pick_poisson_det_multipartition_kappa2_collapse_blockPairs D.blockCount,
    D.crossFactor pair.1 pair.2

/-- The uniform kappa-square scale envelope from replacing every cross factor by `rho0 ^ 2`. -/
def kappa2Envelope
    (D : xi_pick_poisson_det_multipartition_kappa2_collapse_data) : ℝ :=
  (D.rho0 ^ 2) ^
    (xi_pick_poisson_det_multipartition_kappa2_collapse_blockPairs D.blockCount).card

/-- The determinant splits into block-internal and cross-block products. -/
def detFactorization
    (D : xi_pick_poisson_det_multipartition_kappa2_collapse_data) : Prop :=
  D.detP = D.blockInternalProduct * D.crossBlockProduct

/-- Every cross-block factor obeys the same minimum-separation upper bound. -/
def uniformMinSeparationBound
    (D : xi_pick_poisson_det_multipartition_kappa2_collapse_data) : Prop :=
  ∀ i j, i < j → D.crossFactor i j ≤ D.rho0 ^ 2

/-- Multiplying the uniform pairwise bound gives the full multipartition kappa-square envelope. -/
def kappa2CollapseBound
    (D : xi_pick_poisson_det_multipartition_kappa2_collapse_data) : Prop :=
  D.crossBlockProduct ≤ D.kappa2Envelope

end xi_pick_poisson_det_multipartition_kappa2_collapse_data

/-- Paper label: `cor:xi-pick-poisson-det-multipartition-kappa2-collapse`. -/
theorem paper_xi_pick_poisson_det_multipartition_kappa2_collapse
    (D : xi_pick_poisson_det_multipartition_kappa2_collapse_data) :
    D.detFactorization ∧ D.uniformMinSeparationBound ∧ D.kappa2CollapseBound := by
  let pairSet :=
    xi_pick_poisson_det_multipartition_kappa2_collapse_blockPairs D.blockCount
  have hdet : D.detFactorization := by
    simpa [xi_pick_poisson_det_multipartition_kappa2_collapse_data.detFactorization,
      xi_pick_poisson_det_multipartition_kappa2_collapse_data.blockInternalProduct,
      xi_pick_poisson_det_multipartition_kappa2_collapse_data.crossBlockProduct, pairSet]
      using D.hdetP
  have huniform : D.uniformMinSeparationBound := D.hcrossFactor_le
  have hcollapse : D.kappa2CollapseBound := by
    have hprod :
        (∏ pair ∈ pairSet, D.crossFactor pair.1 pair.2) ≤
          ∏ _pair ∈ pairSet, D.rho0 ^ 2 := by
      refine Finset.prod_le_prod ?_ ?_
      · intro pair _hpair
        exact D.hcrossFactor_nonneg pair.1 pair.2
      · intro pair hpair
        exact D.hcrossFactor_le pair.1 pair.2 (Finset.mem_filter.mp hpair).2
    simpa [xi_pick_poisson_det_multipartition_kappa2_collapse_data.kappa2CollapseBound,
      xi_pick_poisson_det_multipartition_kappa2_collapse_data.crossBlockProduct,
      xi_pick_poisson_det_multipartition_kappa2_collapse_data.kappa2Envelope, pairSet]
      using hprod
  exact ⟨hdet, huniform, hcollapse⟩

end Omega.Zeta
