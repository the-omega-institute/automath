import Mathlib.Data.Nat.Basic

namespace Omega.POM

/-- Concrete arithmetic data for the mod-`3` resonance discriminant package at `q = 13, 15`.
The mod-`3` gcd degree is the listed value `8`, and the discriminant factorization carries
the corresponding explicit power of `3`. -/
structure pom_resonance_disc_3adic_q13_15_data where
  pom_resonance_disc_3adic_q13_15_gcd_degree : ℕ
  discriminant : ℕ
  pom_resonance_disc_3adic_q13_15_residual_factor : ℕ
  pom_resonance_disc_3adic_q13_15_mod3_gcd_degree :
    pom_resonance_disc_3adic_q13_15_gcd_degree = 8
  pom_resonance_disc_3adic_q13_15_discriminant_factorization :
    discriminant =
      3 ^ pom_resonance_disc_3adic_q13_15_gcd_degree *
        pom_resonance_disc_3adic_q13_15_residual_factor

/-- Paper label: `thm:pom-resonance-disc-3adic-q13-15`. Once the mod-`3` resonance package
identifies a common factor of degree `8`, the discriminant carries the corresponding `3`-power. -/
theorem paper_pom_resonance_disc_3adic_q13_15
    (D : pom_resonance_disc_3adic_q13_15_data) : 3 ^ 8 ∣ D.discriminant := by
  rw [D.pom_resonance_disc_3adic_q13_15_discriminant_factorization,
    D.pom_resonance_disc_3adic_q13_15_mod3_gcd_degree]
  exact ⟨D.pom_resonance_disc_3adic_q13_15_residual_factor, rfl⟩

end Omega.POM
