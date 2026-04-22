import Mathlib
import Omega.Conclusion.FoldOutputEntropyGaugeAffineIdentity
import Omega.OperatorAlgebra.FoldInfoNCEMILimit

open Filter Topology

namespace Omega.Conclusion

noncomputable section

/-- Concrete large-`K` visible-entropy complement statement for one finite layer `m`. -/
def conclusion_infonce_large_k_visible_entropy_complement_statement
    (D : FoldOutputEntropyGaugeAffineIdentityData) : Prop :=
  Tendsto
      (fun K : ℕ => Real.log (K : ℝ) - Omega.OperatorAlgebra.foldInfoNCELossInfimum D.m K)
      atTop (𝓝 (Omega.OperatorAlgebra.foldInfoNCEVisibleEntropy D.m)) ∧
    Omega.OperatorAlgebra.foldInfoNCEVisibleEntropy D.m = (D.m : ℝ) * Real.log 2 ∧
    D.kappaIdentity ∧
    D.gaugeDensityAsymptotic

theorem conclusion_infonce_large_k_visible_entropy_complement_package
    (D : FoldOutputEntropyGaugeAffineIdentityData) :
    conclusion_infonce_large_k_visible_entropy_complement_statement D := by
  rcases Omega.OperatorAlgebra.paper_op_algebra_fold_infonce_mi_limit D.m with
    ⟨_hmi, _hopt, hlim⟩
  rcases paper_conclusion_fold_output_entropy_gauge_affine_identity D with ⟨hkappa, hgauge⟩
  refine ⟨hlim, by simp [Omega.OperatorAlgebra.foldInfoNCEVisibleEntropy], hkappa, hgauge⟩

/-- Paper wrapper for the large-negative-sample visible-entropy complement law. The current Lean
package records exactly the ingredients used in the paper proof: the `K → ∞` InfoNCE limit,
the direct rewrite `H(μ_m) = m log 2 - κ_m`, and the first-order affine relation between `g_m`
and the entropy term.
    cor:conclusion-infonce-large-k-visible-entropy-complement -/
theorem paper_conclusion_infonce_large_k_visible_entropy_complement
    (D : FoldOutputEntropyGaugeAffineIdentityData) :
    conclusion_infonce_large_k_visible_entropy_complement_statement D := by
  exact conclusion_infonce_large_k_visible_entropy_complement_package D

end

end Omega.Conclusion
