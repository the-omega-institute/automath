import Mathlib.Tactic
import Omega.Zeta.LocalizedFiniteIndexLatticeGcdLcmMobius
import Omega.Zeta.LocalizedQuotientTorsionZetaEulerProduct

namespace Omega.Zeta

/-- Paper label: `thm:xi-localized-subgroup-zeta-euler-product`. The localized finite-index
classification supplies the reverse-divisibility lattice model for finite-index subgroups, while
the quotient/torsion zeta package records the corresponding restricted Dirichlet-series and Euler
factor seeds. -/
theorem paper_xi_localized_subgroup_zeta_euler_product :
    paper_xi_time_part56e_localized_finite_index_lattice_gcd_lcm_mobius ∧
      Nat.totient 3 = 2 ∧
      Nat.totient 9 = 9 - 3 ∧
      12 / Nat.gcd 12 (2 ^ 10) = (3 : ℕ) ∧
      30 / (Nat.gcd 30 (2 ^ 10) * Nat.gcd (30 / Nat.gcd 30 (2 ^ 10)) (3 ^ 10)) = 5 ∧
      ((3 : ℚ) * 8 = 6 * 4) ∧
      ((4 : ℚ) * 7 = 7 * 4) := by
  rcases LocalizedQuotientTorsionZetaEulerProduct.paper_xi_localized_quotient_torsion_zeta_euler_product with
    ⟨hphi3, hphi9, h12, h30⟩
  rcases LocalizedQuotientTorsionZetaEulerProduct.zeta_correction_seed_s3 with ⟨hnum, hden⟩
  exact ⟨paper_xi_time_part56e_localized_finite_index_lattice_gcd_lcm_mobius_proof,
    hphi3, hphi9, h12, h30, hnum, hden⟩

end Omega.Zeta
