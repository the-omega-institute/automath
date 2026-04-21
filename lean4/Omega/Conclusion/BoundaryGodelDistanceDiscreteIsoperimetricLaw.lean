import Omega.SPG.DyadicPolyclubeDiscreteIsoperimetry

namespace Omega.Conclusion

/-- Once the boundary Gödel distance of `U △ V` has been identified with the boundary-face count
`F` of that symmetric difference and `NΔ` with its cube count, the discrete dyadic isoperimetry
theorem gives the expected two-sided bounds immediately.
    thm:conclusion-boundary-godel-distance-discrete-isoperimetric-law -/
theorem paper_conclusion_boundary_godel_distance_discrete_isoperimetric_law
    (h : Omega.SPG.DyadicPolyclubeDiscreteIsoperimetryData) (Dist NΔ : ℕ)
    (hDist : Dist = h.F) (hDelta : NΔ = h.N) :
    ((2 * h.n) ^ h.n) * NΔ ^ (h.n - 1) ≤ Dist ^ h.n ∧
      Dist ≤ 2 * h.n * NΔ := by
  simpa [hDist, hDelta] using Omega.SPG.paper_spg_dyadic_polyclube_discrete_isoperimetry h

end Omega.Conclusion
