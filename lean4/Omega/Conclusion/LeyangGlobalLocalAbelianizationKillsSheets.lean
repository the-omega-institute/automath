import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-leyang-global-local-abelianization-kills-sheets`. -/
theorem paper_conclusion_leyang_global_local_abelianization_kills_sheets
    {G A : Type*} [Group G] [CommGroup A] (ρ : G →* A) (g h : G) :
    ρ (g * h * g⁻¹ * h⁻¹) = 1 := by
  simp [map_mul, map_inv]

end Omega.Conclusion
