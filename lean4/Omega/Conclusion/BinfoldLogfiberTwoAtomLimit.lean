import Mathlib.Tactic

namespace Omega.Conclusion

open scoped Topology

/-- Paper label: `thm:conclusion-binfold-logfiber-two-atom-limit`. -/
theorem paper_conclusion_binfold_logfiber_two_atom_limit (φ : ℝ) (hφ : 0 < φ) (p1 err : ℕ → ℝ)
    (hp1 : Filter.Tendsto p1 Filter.atTop (𝓝 (1 / (φ * Real.sqrt 5))))
    (herr : Filter.Tendsto err Filter.atTop (𝓝 0))
    (hvar :
      (1 / (φ * Real.sqrt 5)) * (Real.log φ)^2 -
          ((1 / (φ * Real.sqrt 5)) * Real.log φ)^2 =
        (Real.log φ)^2 / 5) :
    Filter.Tendsto
      (fun m => p1 m * (Real.log φ)^2 - (p1 m * Real.log φ)^2 + err m)
      Filter.atTop (𝓝 ((Real.log φ)^2 / 5)) := by
  have hfirst :
      Filter.Tendsto (fun m => p1 m * (Real.log φ)^2) Filter.atTop
        (𝓝 ((1 / (φ * Real.sqrt 5)) * (Real.log φ)^2)) :=
    hp1.mul tendsto_const_nhds
  have hlinear :
      Filter.Tendsto (fun m => p1 m * Real.log φ) Filter.atTop
        (𝓝 ((1 / (φ * Real.sqrt 5)) * Real.log φ)) :=
    hp1.mul tendsto_const_nhds
  have hmain :
      Filter.Tendsto (fun m => p1 m * (Real.log φ)^2 - (p1 m * Real.log φ)^2)
        Filter.atTop
        (𝓝 ((1 / (φ * Real.sqrt 5)) * (Real.log φ)^2 -
          ((1 / (φ * Real.sqrt 5)) * Real.log φ)^2)) :=
    hfirst.sub (hlinear.pow 2)
  have hcoeff : (Real.sqrt 5)⁻¹ * φ⁻¹ = 1 / (φ * Real.sqrt 5) := by
    field_simp [hφ.ne', (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 5))]
  have htarget :
      (Real.sqrt 5)⁻¹ * φ⁻¹ * (Real.log φ)^2 -
          ((Real.sqrt 5)⁻¹ * φ⁻¹ * Real.log φ)^2 =
        (Real.log φ)^2 / 5 := by
    rw [hcoeff]
    exact hvar
  simpa [htarget] using hmain.add herr

end Omega.Conclusion
