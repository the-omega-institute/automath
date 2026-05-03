import Mathlib

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-renyi2-effective-support-collapse`. -/
theorem paper_conclusion_renyi2_effective_support_collapse
    (Xcard Col Neff : ℕ → ℝ)
    (hXpos : ∀ m, 0 < Xcard m)
    (hColpos : ∀ m, 0 < Col m)
    (hNeff : ∀ m, Neff m = (Col m)⁻¹)
    (hprod : Filter.Tendsto (fun m => Xcard m * Col m) Filter.atTop Filter.atTop) :
    Filter.Tendsto (fun m => Neff m / Xcard m) Filter.atTop (nhds 0) := by
  have hinv :
      Filter.Tendsto (fun m : ℕ => (Xcard m * Col m)⁻¹) Filter.atTop (nhds (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp hprod
  have hrewrite :
      (fun m : ℕ => Neff m / Xcard m) =ᶠ[Filter.atTop]
        fun m : ℕ => (Xcard m * Col m)⁻¹ := by
    filter_upwards with m
    rw [hNeff m]
    field_simp [(hXpos m).ne', (hColpos m).ne']
  exact (Filter.tendsto_congr' hrewrite).2 hinv

end Omega.Conclusion
