import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

/-- Paper label: `cor:gm-sumproduct-exponent-law`. The complementarity exponent can be taken to
be the explicit lower-bound value `κ / (2 * log α)`. -/
theorem paper_gm_sumproduct_exponent_law (α κ : ℝ) (Expansion : ℝ → Prop) (hα : 1 < α)
    (hκ : 0 < κ) (hbase : Expansion (κ / (2 * Real.log α))) :
    ∃ δ : ℝ, 0 < δ ∧ Expansion δ ∧ κ / (2 * Real.log α) ≤ δ := by
  refine ⟨κ / (2 * Real.log α), ?_, hbase, le_rfl⟩
  have hlog : 0 < Real.log α := Real.log_pos hα
  exact div_pos hκ (mul_pos (by norm_num) hlog)

end Omega.SyncKernelWeighted
