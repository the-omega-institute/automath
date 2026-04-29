namespace Omega.Zeta

/-- Paper label: `thm:xi-slice-horizon-carath-toeplitz`. -/
theorem paper_xi_slice_horizon_carath_toeplitz
    (xiZerosOnCriticalLine phiRootsOnCircle caratheodoryPositive toeplitzPsd : Prop)
    (h12 : xiZerosOnCriticalLine ↔ phiRootsOnCircle)
    (h23 : phiRootsOnCircle ↔ caratheodoryPositive)
    (h34 : caratheodoryPositive ↔ toeplitzPsd) :
    (xiZerosOnCriticalLine ↔ phiRootsOnCircle) ∧
      (xiZerosOnCriticalLine ↔ caratheodoryPositive) ∧
        (xiZerosOnCriticalLine ↔ toeplitzPsd) := by
  exact ⟨h12, h12.trans h23, (h12.trans h23).trans h34⟩

end Omega.Zeta
