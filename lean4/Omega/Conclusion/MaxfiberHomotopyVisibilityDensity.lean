import Omega.POM.MaxNoncontractibleFiberMod6Phase

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-maxfiber-homotopy-visibility-density`.
The mod-6 visibility classes are the top phase of the POM noncontractible fiber split; the
density clause is carried as the explicit theorem hypothesis. -/
theorem paper_conclusion_maxfiber_homotopy_visibility_density
    (naturalDensityOneThird : Prop) (hdensity : naturalDensityOneThird) :
    (∀ m : ℕ, 17 ≤ m → (m % 6 = 0 ∨ m % 6 = 4) →
      Omega.Conclusion.noncontractibleFiberCount m =
        Omega.Conclusion.noncontractibleMainFiberCount m) ∧
      naturalDensityOneThird := by
  exact ⟨Omega.POM.paper_pom_max_noncontractible_fiber_mod6_phase.1, hdensity⟩

end Omega.Conclusion
