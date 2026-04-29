import Omega.POM.FiberGeodesicLog2Pi
import Omega.POM.OrderPolytopeVolumeLinext

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-zigzag-replay-entropy-orderpoly-density-identity`. -/
theorem paper_conclusion_zigzag_replay_entropy_orderpoly_density_identity :
    Omega.POM.pom_fiber_geodesic_log2pi_statement ∧
      (∀ N : ℕ,
        Omega.POM.OrderPolytopeVolumeLinext (Omega.POM.fenceDisjointUnionPoset [N])) := by
  refine ⟨Omega.POM.paper_pom_fiber_geodesic_log2pi, ?_⟩
  intro N
  exact Omega.POM.paper_pom_order_polytope_volume_linext
    (Omega.POM.fenceDisjointUnionPoset [N])

end Omega.Conclusion
