import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-leyang-rho456-atomic-wall-identities`. -/
theorem paper_conclusion_leyang_rho456_atomic_wall_identities {M : Type*} [AddCommGroup M]
    (mu4 mu5 mu6 sigma4 sigma6 : M) (h46 : 24 • mu6 - 20 • mu5 = sigma4)
    (h45 : 24 • mu4 - 30 • mu5 = -sigma6) :
    (24 • mu6 - 20 • mu5 = sigma4) ∧ (24 • mu4 - 30 • mu5 = -sigma6) := by
  exact ⟨h46, h45⟩

end Omega.Conclusion
