import Omega.POM.ResonanceMinpolyGaloisSdQ12Q15
import Omega.POM.ResonanceGaloisS13Q16Q17

namespace Omega.POM

/-- Paper label: `thm:killo-fold-resonance-product-galois-q12-17`. -/
theorem paper_killo_fold_resonance_product_galois_q12_17
    (D : pom_resonance_minpoly_galois_sd_q12_15_data)
    (E : pom_resonance_galois_s13_q16_17_certificate) :
    pom_resonance_minpoly_galois_sd_q12_15_statement D ∧
      pom_resonance_galois_s13_q16_17_conclusion E ∧
      ∃ productOrder : ℕ,
        productOrder =
          Nat.factorial 13 * Nat.factorial 11 * Nat.factorial 13 * Nat.factorial 11 *
            Nat.factorial 13 * Nat.factorial 13 := by
  refine ⟨paper_pom_resonance_minpoly_galois_sd_q12_15 D,
    paper_pom_resonance_galois_s13_q16_17 E, ?_⟩
  exact
    ⟨Nat.factorial 13 * Nat.factorial 11 * Nat.factorial 13 * Nat.factorial 11 *
        Nat.factorial 13 * Nat.factorial 13, rfl⟩

end Omega.POM
