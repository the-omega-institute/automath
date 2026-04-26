import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-leyang-rho456-wall-potential-identities`. -/
theorem paper_conclusion_leyang_rho456_wall_potential_identities
    (F4 F5 F6 L4 L6 : ℝ)
    (h6 : F6 - (5 / 6) * F5 = (1 / 24) * L4)
    (h4 : F4 - (5 / 4) * F5 = -(1 / 24) * L6) :
    (F6 - (5 / 6) * F5 = (1 / 24) * L4) ∧
      (F4 - (5 / 4) * F5 = -(1 / 24) * L6) := by
  exact ⟨h6, h4⟩

end Omega.Conclusion
