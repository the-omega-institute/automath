import Omega.Zeta.XiEdBivariateDoubleDiscriminantIdentities

namespace Omega.Zeta

/-- Paper label: `prop:xi-ed-resultant-ramification-intrinsic`. -/
theorem paper_xi_ed_resultant_ramification_intrinsic :
    (∀ y : ℤ,
      xi_ed_bivariate_double_discriminant_identities_cubicDiscriminant y =
        -y ^ 3 * (y - 1) * xi_ed_bivariate_double_discriminant_identities_g y) ∧
      (∀ m : ℤ,
        xi_ed_bivariate_double_discriminant_identities_B m ^ 2 -
            4 * xi_ed_bivariate_double_discriminant_identities_A m * (4 * m - 7) =
          -4 * m ^ 3 - 16 * m ^ 2 + 16 * m + 65) := by
  rcases paper_xi_ed_bivariate_double_discriminant_identities with ⟨hm, hy⟩
  exact ⟨fun y => (hy y).1, hm⟩

end Omega.Zeta
