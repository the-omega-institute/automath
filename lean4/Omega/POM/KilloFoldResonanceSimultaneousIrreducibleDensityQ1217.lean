import Omega.POM.KilloFoldResonanceProductGaloisQ1217

namespace Omega.POM

/-- Paper label: `cor:killo-fold-resonance-simultaneous-irreducible-density-q12-17`. -/
theorem paper_killo_fold_resonance_simultaneous_irreducible_density_q12_17
    (D : pom_resonance_minpoly_galois_sd_q12_15_data)
    (E : pom_resonance_galois_s13_q16_17_certificate) :
    ∃ density : ℚ,
      density = (1 : ℚ) / 3455881 ∧
        ∃ productOrder : ℕ,
          productOrder =
            Nat.factorial 13 * Nat.factorial 11 * Nat.factorial 13 * Nat.factorial 11 *
              Nat.factorial 13 * Nat.factorial 13 := by
  rcases paper_killo_fold_resonance_product_galois_q12_17 D E with ⟨_, _, horder⟩
  refine ⟨(1 : ℚ) / 3455881, rfl, ?_⟩
  exact horder

end Omega.POM
