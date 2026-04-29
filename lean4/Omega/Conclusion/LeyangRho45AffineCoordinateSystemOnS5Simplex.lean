import Mathlib.Tactic
import Omega.Conclusion.LeyangS5TwoChannelMinimalCompleteness

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-leyang-rho45-affine-coordinate-system-on-s5-simplex`. The six
`ρ₅/ρ₄` coordinates admit the explicit inverse formulas already recorded in the audited
two-channel completeness package, hence every normalized `S₅` density vector is recovered from its
coordinates and the coordinate map is injective on the simplex of normalized class densities. -/
theorem paper_conclusion_leyang_rho45_affine_coordinate_system_on_s5_simplex :
    (∀ v : LeyangS5DensityVector, IsNormalizedDensity v →
      recoveredDensityVector (twoChannelCoordinates v) = v) ∧
      ∀ v w : LeyangS5DensityVector, IsNormalizedDensity v → IsNormalizedDensity w →
        twoChannelCoordinates v = twoChannelCoordinates w → v = w := by
  have hrecover : ∀ v : LeyangS5DensityVector, IsNormalizedDensity v →
      recoveredDensityVector (twoChannelCoordinates v) = v := by
    intro v hv
    let D : LeyangS5TwoChannelData := ⟨twoChannelCoordinates v⟩
    exact (paper_conclusion_leyang_s5_two_channel_minimal_completeness D).1 v hv rfl |>.symm
  refine ⟨?_, ?_⟩
  · exact hrecover
  · intro v w hv hw hcoords
    calc
      v = recoveredDensityVector (twoChannelCoordinates v) := by
        symm
        exact hrecover v hv
      _ = recoveredDensityVector (twoChannelCoordinates w) := by simp [hcoords]
      _ = w := hrecover w hw

end Omega.Conclusion
