import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- `σ` is the local sixfold branch scale at the Xi-center parameter `α`. Concretely this means
`σ^6 = |α - 1/2|`; keeping `σ` explicit avoids committing the theorem to a specific choice of
real sixth root implementation. -/
def xiCenterSixfoldScale (α σ : ℝ) : Prop :=
  0 ≤ σ ∧ σ ^ 6 = |α - (1 / 2 : ℝ)|

/-- If the node separation is bounded above by the sixfold branch scale and a generic
`sep^{-(κ-1)}` inversion lower bound is available, then one gets the corresponding
`|α - 1/2|^{-(κ-1)/6}`-type blowup after substituting the sixfold scale.
    thm:xi-center-sixfold-kappa-node-inversion-blowup -/
theorem paper_xi_center_sixfold_kappa_node_inversion_blowup
    (κ : ℕ) (hκ : 2 ≤ κ) (α u σ sep L cBranch cSplit C : ℝ)
    (hσ : xiCenterSixfoldScale α σ) (hBranch : 0 < cBranch) (hSplit : 0 < cSplit)
    (hC : 0 ≤ C) (hu : |u - 1| ≤ cBranch * σ) (hsep : sep ≤ cSplit * |u - 1|)
    (hsep_pos : 0 < sep) (hL : C / sep ^ (κ - 1) ≤ L) :
    C / (cSplit * cBranch * σ) ^ (κ - 1) ≤ L := by
  let _ := hκ
  rcases hσ with ⟨hσ_nonneg, _hσ_eq⟩
  have hsep_scale : sep ≤ cSplit * (cBranch * σ) := by
    calc
      sep ≤ cSplit * |u - 1| := hsep
      _ ≤ cSplit * (cBranch * σ) := by
        gcongr
  have hbase_nonneg : 0 ≤ cSplit * cBranch * σ := by positivity
  have hbase_pos : 0 < cSplit * cBranch * σ := by
    exact lt_of_lt_of_le hsep_pos (by simpa [mul_assoc] using hsep_scale)
  have hpow : sep ^ (κ - 1) ≤ (cSplit * cBranch * σ) ^ (κ - 1) := by
    gcongr
    simpa [mul_assoc] using hsep_scale
  have hsep_pow_pos : 0 < sep ^ (κ - 1) := by
    exact pow_pos hsep_pos _
  have hdiv :
      C / (cSplit * cBranch * σ) ^ (κ - 1) ≤ C / sep ^ (κ - 1) := by
    exact div_le_div_of_nonneg_left hC hsep_pow_pos hpow
  exact hdiv.trans hL

end Omega.Zeta
