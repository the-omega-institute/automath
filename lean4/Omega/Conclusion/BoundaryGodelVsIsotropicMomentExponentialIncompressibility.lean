import Omega.Conclusion.BoundaryStokesObservationMinimalDimension
import Omega.SPG.BoundaryGodelMomentReadout

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-boundary-godel-vs-isotropic-moment-exponential-incompressibility`.
If a composed isotropic sketch `Ψₘ ∘ M_{rₘ}` is injective, then the moment map itself is already
injective, so the existing anisotropy-gap lower bound applies. In parallel, the chapter's
boundary Gödel code remains injective on the fixed-resolution class. -/
theorem paper_conclusion_boundary_godel_vs_isotropic_moment_exponential_incompressibility
    (m n r_m : ℕ) {Y_m : Type*} (momentMap : Fin (2 ^ (m * n)) → Fin r_m)
    (postSketch : Fin r_m → Y_m)
    (hSketch : Function.Injective fun u => postSketch (momentMap u)) :
    Function.Injective (Omega.SPG.boundaryGodelCode : Omega.SPG.DyadicPolycube →
      Omega.SPG.BoundaryGodelCode) ∧
      Function.Injective momentMap ∧
      2 ^ (m * n) ≤ r_m := by
  have hMoment : Function.Injective momentMap := by
    intro u v huv
    exact hSketch (by simp [huv])
  have hBoundary :
      Function.Injective (Omega.SPG.boundaryGodelCode : Omega.SPG.DyadicPolycube →
        Omega.SPG.BoundaryGodelCode) := by
    intro U V _
    cases U
    cases V
    rfl
  have hGap :
      2 ^ (m * n) ≤ r_m :=
    paper_conclusion_boundary_stokes_observation_minimal_dimension_seeds
      m n r_m momentMap hMoment
  exact ⟨hBoundary, hMoment, hGap⟩

end Omega.Conclusion
