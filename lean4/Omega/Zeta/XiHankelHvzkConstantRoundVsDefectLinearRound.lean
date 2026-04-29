namespace Omega.Zeta

/-- Paper label: `cor:xi-hankel-hvzk-constant-round-vs-defect-linear-round`. -/
theorem paper_xi_hankel_hvzk_constant_round_vs_defect_linear_round
    (standardHVZK constantRoundProtocol defectLinearRoundLaw extraInterfaceConstraint : Prop)
    (hconstant : standardHVZK -> constantRoundProtocol)
    (hneeds : constantRoundProtocol -> defectLinearRoundLaw -> extraInterfaceConstraint) :
    standardHVZK -> defectLinearRoundLaw -> extraInterfaceConstraint := by
  intro hstandard hdefect
  exact hneeds (hconstant hstandard) hdefect

end Omega.Zeta
