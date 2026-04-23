namespace Omega.Zeta

/-- Paper label: `thm:xi-cartesian-power-leyang-double-atom-tangent-clt`.
Packages the double-atom condensation and the upper/lower tangent CLT channels into a single
certificate. -/
theorem paper_xi_cartesian_power_leyang_double_atom_tangent_clt
    (doubleAtomCondensation upperTangentCLT lowerTangentCLT : Prop)
    (hCondense : doubleAtomCondensation) (hUpper : upperTangentCLT) (hLower : lowerTangentCLT) :
    doubleAtomCondensation ∧ upperTangentCLT ∧ lowerTangentCLT := by
  exact ⟨hCondense, hUpper, hLower⟩

end Omega.Zeta
