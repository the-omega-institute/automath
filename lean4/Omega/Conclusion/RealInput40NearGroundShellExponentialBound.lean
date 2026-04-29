namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-realinput40-near-ground-shell-exponential-bound`. -/
theorem paper_conclusion_realinput40_near_ground_shell_exponential_bound
    (chernoffBound microcanonicalCuspExpansion nearGroundShellBound endpointValueCompatibility : Prop)
    (hchernoff : chernoffBound)
    (hcusp : chernoffBound -> microcanonicalCuspExpansion -> nearGroundShellBound)
    (hendpoint : nearGroundShellBound -> endpointValueCompatibility)
    (hexpansion : microcanonicalCuspExpansion) :
    nearGroundShellBound ∧ endpointValueCompatibility := by
  have hnear : nearGroundShellBound := hcusp hchernoff hexpansion
  exact ⟨hnear, hendpoint hnear⟩

end Omega.Conclusion
