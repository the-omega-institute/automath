import Mathlib.Tactic
import Omega.Zeta.XiLocalizedSubgroupZetaEulerProduct
import Omega.Zeta.XiTimePart69cLocalizedFiniteIndexSubgroupClassification

namespace Omega.Zeta

/-- Paper label: `cor:xi-time-part69c-localized-finite-index-lattice-zeta`. -/
theorem paper_xi_time_part69c_localized_finite_index_lattice_zeta :
    xi_time_part69c_localized_finite_index_subgroup_classification_statement ∧
      paper_xi_time_part56e_localized_finite_index_lattice_gcd_lcm_mobius ∧
        Nat.totient 3 = 2 ∧
          Nat.totient 9 = 9 - 3 ∧
            12 / Nat.gcd 12 (2 ^ 10) = (3 : ℕ) ∧
              30 / (Nat.gcd 30 (2 ^ 10) *
                    Nat.gcd (30 / Nat.gcd 30 (2 ^ 10)) (3 ^ 10)) = 5 ∧
                ((3 : ℚ) * 8 = 6 * 4) ∧
                  ((4 : ℚ) * 7 = 7 * 4) := by
  rcases paper_xi_localized_subgroup_zeta_euler_product with
    ⟨hlattice, hphi3, hphi9, h12, h30, hseedA, hseedB⟩
  exact ⟨paper_xi_time_part69c_localized_finite_index_subgroup_classification,
    hlattice, hphi3, hphi9, h12, h30, hseedA, hseedB⟩

end Omega.Zeta
