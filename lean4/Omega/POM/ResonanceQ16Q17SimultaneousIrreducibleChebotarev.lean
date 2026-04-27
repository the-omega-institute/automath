import Omega.POM.ResonanceQ16Q17LinearlyDisjoint

namespace Omega.POM

/-- Paper label: `thm:pom-resonance-q16-q17-simultaneous-irreducible-chebotarev`. -/
theorem paper_pom_resonance_q16_q17_simultaneous_irreducible_chebotarev :
    pom_resonance_q16_q17_linearly_disjoint_galois_product ∧
      pom_resonance_s13_frobenius_cycle_certificate_q16_q17_jordanPackage 16 ∧
      pom_resonance_s13_frobenius_cycle_certificate_q16_q17_jordanPackage 17 ∧
      ((1 : ℚ) / (13 ^ 2) = 1 / 169) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact paper_pom_resonance_q16_q17_linearly_disjoint.2
  · exact pom_resonance_s13_frobenius_cycle_certificate_q16_q17_certificateAt_16.2.2.2
  · exact pom_resonance_s13_frobenius_cycle_certificate_q16_q17_certificateAt_17.2.2.2
  · norm_num

end Omega.POM
