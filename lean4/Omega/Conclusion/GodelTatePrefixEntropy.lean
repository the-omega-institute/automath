import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-godel-tate-prefix-entropy`.
After discarding the initial `k = 0` term, the normalized logarithm is identically
`Real.log (M + 1)`. -/
theorem paper_conclusion_godel_tate_prefix_entropy (M : Nat) :
    Filter.Tendsto (fun k : Nat => Real.log ((M + 1 : ℝ) ^ k) / (k : ℝ)) Filter.atTop
      (nhds (Real.log (M + 1))) := by
  have heq :
      (fun k : Nat => Real.log ((M + 1 : ℝ) ^ k) / (k : ℝ)) =ᶠ[Filter.atTop]
        fun _ : Nat => Real.log (M + 1 : ℝ) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with k hk
    have hk_pos : 0 < (k : ℝ) := by exact_mod_cast hk
    have hk_ne : (k : ℝ) ≠ 0 := ne_of_gt hk_pos
    rw [Real.log_pow]
    field_simp [hk_ne]
  exact Filter.Tendsto.congr' heq.symm tendsto_const_nhds

end Omega.Conclusion
