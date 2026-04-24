import Mathlib.Data.Nat.Basic

namespace Omega.POM

/-- Concrete arithmetic data for the dyadic resonance discriminant package. The mod-`2` gcd degree
matches `degree - 1`, and the discriminant carries the corresponding explicit power of `2`. -/
structure pom_resonance_disc_2adic_thickness_lb_data where
  degree : ℕ
  pom_resonance_disc_2adic_thickness_lb_gcd_degree : ℕ
  discriminant : ℕ
  pom_resonance_disc_2adic_thickness_lb_residual_factor : ℕ
  pom_resonance_disc_2adic_thickness_lb_mod2_gcd_degree :
    pom_resonance_disc_2adic_thickness_lb_gcd_degree = degree - 1
  pom_resonance_disc_2adic_thickness_lb_discriminant_factorization :
    discriminant =
      2 ^ pom_resonance_disc_2adic_thickness_lb_gcd_degree *
        pom_resonance_disc_2adic_thickness_lb_residual_factor

/-- Paper label: `thm:pom-resonance-disc-2adic-thickness-lb`. Once the mod-`2` resonance package
identifies a common factor of degree `d_q - 1`, the discriminant carries the same explicit
`2`-power. -/
theorem paper_pom_resonance_disc_2adic_thickness_lb (D : pom_resonance_disc_2adic_thickness_lb_data) :
    2 ^ (D.degree - 1) ∣ D.discriminant := by
  rw [D.pom_resonance_disc_2adic_thickness_lb_discriminant_factorization,
    D.pom_resonance_disc_2adic_thickness_lb_mod2_gcd_degree]
  exact ⟨D.pom_resonance_disc_2adic_thickness_lb_residual_factor, by
    rw [Nat.mul_comm]⟩

end Omega.POM
