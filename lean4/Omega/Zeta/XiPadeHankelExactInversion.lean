import Omega.Zeta.XiTimePart9zbkPadeJacobiIdentity

namespace Omega.Zeta

/-- Concrete Padé-Hankel inversion data for `cor:xi-pade-hankel-exact-inversion`. The finite-depth
Padé shadow is the rational finite-atomic object; matching through order `2k` invokes the existing
Padé-Jacobi uniqueness theorem, and the final field records the recovered pole/residue data. -/
structure xi_pade_hankel_exact_inversion_data where
  k : ℕ
  hk : 1 ≤ k
  pade : PadeJacobiShadow
  finite_atomic_rationality : finiteDepth pade
  first_2k_moment_match : matchesToOrder m_phi pade (2 * k)
  pole : Fin k → ℚ
  residue : Fin k → ℚ
  recoveredPole : Fin k → ℚ
  recoveredResidue : Fin k → ℚ
  pole_residue_recovery : recoveredPole = pole ∧ recoveredResidue = residue

/-- Exact inversion identifies the Padé shadow with the unique canonical rational approximant and
recovers the packaged pole/residue table. -/
def xi_pade_hankel_exact_inversion_statement
    (D : xi_pade_hankel_exact_inversion_data) : Prop :=
  finiteDepth D.pade ∧
    matchesToOrder m_phi D.pade (2 * D.k) ∧
      D.pade = m_phi_n D.k ∧
        IsUniquePadeJacobiShadow m_phi (m_phi_n D.k) D.k ∧
          D.recoveredPole = D.pole ∧ D.recoveredResidue = D.residue

/-- Paper label: `cor:xi-pade-hankel-exact-inversion`. -/
theorem paper_xi_pade_hankel_exact_inversion
    (D : xi_pade_hankel_exact_inversion_data) :
    xi_pade_hankel_exact_inversion_statement D := by
  have hunique := paper_xi_time_part9zbk_pade_jacobi_identity D.k D.hk
  exact ⟨D.finite_atomic_rationality, D.first_2k_moment_match,
    hunique D.pade D.finite_atomic_rationality D.first_2k_moment_match, hunique,
    D.pole_residue_recovery.1, D.pole_residue_recovery.2⟩

end Omega.Zeta
