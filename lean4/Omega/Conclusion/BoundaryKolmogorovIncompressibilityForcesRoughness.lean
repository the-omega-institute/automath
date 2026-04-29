import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-boundary-kolmogorov-incompressibility-forces-roughness`. -/
theorem paper_conclusion_boundary_kolmogorov_incompressibility_forces_roughness
    (n m : Nat) (K F C kappa : ℝ) (hm : 0 < (m : ℝ)) (hC : 0 < C)
    (hK : kappa * (2 : ℝ) ^ (m * n) ≤ K) (hUpper : K ≤ C * (m : ℝ) * F) :
    kappa * (2 : ℝ) ^ (m * n) / (C * (m : ℝ)) ≤ F := by
  have hden : 0 < C * (m : ℝ) := mul_pos hC hm
  rw [div_le_iff₀ hden]
  calc
    kappa * (2 : ℝ) ^ (m * n) ≤ K := hK
    _ ≤ C * (m : ℝ) * F := hUpper
    _ = F * (C * (m : ℝ)) := by ring

end Omega.Conclusion
