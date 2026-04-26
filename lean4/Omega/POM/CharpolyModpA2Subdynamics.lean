import Omega.POM.CharpolyModpA2Embedding

namespace Omega.POM

/-- The audited `(q, p) = (14, 7)` slice exposes the `A₂` factor. -/
theorem pom_charpoly_modp_a2_subdynamics_mod7_factor :
    ∃ Q : Polynomial (ZMod 7), resonancePoly14Mod7 = chiA2Mod7 * Q := by
  exact ⟨resonanceCofactor14Mod7, resonancePoly14Mod7_factorization⟩

/-- The audited `(q, p) = (12, 11)` slice exposes the `A₂` factor. -/
theorem pom_charpoly_modp_a2_subdynamics_mod11_factor :
    ∃ Q : Polynomial (ZMod 11), resonancePoly12Mod11 = chiA2Mod11 * Q := by
  exact ⟨resonanceCofactor12Mod11, resonancePoly12Mod11_factorization⟩

/-- The concrete subdynamics factor-extraction interface for the two audited finite-field slices.
    cor:pom-charpoly-modp-a2-subdynamics -/
theorem paper_pom_charpoly_modp_a2_subdynamics :
    (∃ Q : Polynomial (ZMod 7), resonancePoly14Mod7 = chiA2Mod7 * Q) ∧
      (∃ Q : Polynomial (ZMod 11), resonancePoly12Mod11 = chiA2Mod11 * Q) := by
  exact ⟨pom_charpoly_modp_a2_subdynamics_mod7_factor,
    pom_charpoly_modp_a2_subdynamics_mod11_factor⟩

end Omega.POM
