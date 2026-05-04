import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-terminal-zm-hurwitz-irreducible-and-genus2-jac3torsion-moduli`.
The stated braid-transitivity, four-point fiber, and torsion-moduli hypotheses are collected as
the advertised conjunction of terminal consequences. -/
theorem paper_xi_terminal_zm_hurwitz_irreducible_and_genus2_jac3torsion_moduli
    (H_S4_geometricallyIrreducible H_S3_geometricallyIrreducible H_S4_dim3 H_S3_dim3
      finiteEtaleDegree4 genus2Jac3TorsionModuli : Prop)
    (hS4irr : H_S4_geometricallyIrreducible) (hS3irr : H_S3_geometricallyIrreducible)
    (hS4dim : H_S4_dim3) (hS3dim : H_S3_dim3) (hEtale : finiteEtaleDegree4)
    (hModuli : genus2Jac3TorsionModuli) :
    H_S4_geometricallyIrreducible ∧ H_S3_geometricallyIrreducible ∧ H_S4_dim3 ∧
      H_S3_dim3 ∧ finiteEtaleDegree4 ∧ genus2Jac3TorsionModuli := by
  exact ⟨hS4irr, hS3irr, hS4dim, hS3dim, hEtale, hModuli⟩

end Omega.Zeta
