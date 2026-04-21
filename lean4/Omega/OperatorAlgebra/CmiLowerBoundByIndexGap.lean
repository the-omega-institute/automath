import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.OperatorAlgebra.IndexSubmultiplicativityCommutingSquare
import Omega.OperatorAlgebra.JonesScalarEqualsExpMinusGap

namespace Omega.OperatorAlgebra

noncomputable section

/-- Paper label: `cor:op-algebra-cmi-lower-bound-by-index-gap`.
Given a hypothesis-level lower bound of the conditional mutual information by the Jones index gap,
the commuting-square index inequality implies that the gap is nonnegative. -/
theorem paper_op_algebra_cmi_lower_bound_by_index_gap
    {ind1 ind2 ind12 cmi : ℝ}
    (h1 : 0 < ind1) (h2 : 0 < ind2) (h12 : 0 < ind12)
    (hcomp : ind12⁻¹ ≥ ind1⁻¹ * ind2⁻¹)
    (hcmi : indexGap ind1 ind2 ind12 ≤ cmi) :
    indexGap ind1 ind2 ind12 ≤ cmi ∧ 0 ≤ indexGap ind1 ind2 ind12 := by
  have hsub :
      ind12 ≤ ind1 * ind2 :=
    paper_op_algebra_index_submultiplicativity_commuting_square h1 h2 h12 hcomp
  have hratio : 1 ≤ (ind1 * ind2) / ind12 := by
    exact (one_le_div h12).2 hsub
  have hgap_nonneg : 0 ≤ indexGap ind1 ind2 ind12 := by
    unfold indexGap
    exact Real.log_nonneg hratio
  exact ⟨hcmi, hgap_nonneg⟩

end

end Omega.OperatorAlgebra
