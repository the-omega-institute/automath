import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace Omega.Conclusion

open Filter Topology

/-- Paper label: `cor:conclusion-squarefree-audit-breakdown`. -/
theorem paper_conclusion_squarefree_audit_breakdown {k : ℕ} (hk : 0 < k) {eps : ℝ}
    (heps : 0 < eps) : ∃ m0 : ℕ, ∀ m ≥ m0, 2 ^ (-(m : ℝ) / k) < eps := by
  have hk_real_pos : 0 < (k : ℝ) := by exact_mod_cast hk
  have hk_real_ne : (k : ℝ) ≠ 0 := ne_of_gt hk_real_pos
  have hcoef_neg : -Real.log (2 : ℝ) / (k : ℝ) < 0 := by
    exact div_neg_of_neg_of_pos (neg_neg_of_pos (Real.log_pos (by norm_num))) hk_real_pos
  have hlin :
      Tendsto (fun m : ℕ => (-Real.log (2 : ℝ) / (k : ℝ)) * (m : ℝ)) atTop atBot := by
    exact tendsto_natCast_atTop_atTop.const_mul_atTop_of_neg hcoef_neg
  have hpow :
      Tendsto (fun m : ℕ => (2 : ℝ) ^ (-(m : ℝ) / (k : ℝ))) atTop (𝓝 0) := by
    have hrew :
        (fun m : ℕ => (2 : ℝ) ^ (-(m : ℝ) / (k : ℝ))) =
          fun m : ℕ => Real.exp ((-Real.log (2 : ℝ) / (k : ℝ)) * (m : ℝ)) := by
      funext m
      rw [Real.rpow_def_of_pos (by norm_num : 0 < (2 : ℝ))]
      congr 1
      field_simp [hk_real_ne]
    rw [hrew]
    exact Real.tendsto_exp_atBot.comp hlin
  have hsmall : ∀ᶠ m : ℕ in atTop, (2 : ℝ) ^ (-(m : ℝ) / (k : ℝ)) < eps := by
    exact hpow.eventually (Iio_mem_nhds heps)
  rcases eventually_atTop.mp hsmall with ⟨m0, hm0⟩
  exact ⟨m0, hm0⟩

end Omega.Conclusion
