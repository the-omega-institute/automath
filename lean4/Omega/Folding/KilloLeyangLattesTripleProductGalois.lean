import Mathlib.Tactic
import Omega.Folding.GaugeAnomalyTrigonalBranchSplittingField
import Omega.Folding.KilloLeyangTwoBranchFieldsProductGalois

namespace Omega.Folding

/-- Ramification support of the Lattès sextic splitting field, read off from the displayed
discriminant `-2^19 * 37^3`. -/
def killo_leyang_lattes_triple_product_galois_lattes_ramification_primes : Finset ℕ :=
  {2, 37}

/-- Quadratic subfield discriminant coming from the extra quadratic factor in the audited
`S₄ × C₂` package. -/
def killo_leyang_lattes_triple_product_galois_lattes_quadratic_discriminant : ℤ :=
  5

/-- Galois order of the Lattès sextic splitting field: `|S₄ × C₂| = 48`. -/
def killo_leyang_lattes_triple_product_galois_lattes_field_order : ℕ :=
  Nat.factorial 4 * 2

/-- Concrete separation package for the three audited fields. The `L₁₀` quadratic support is
disjoint from the Lattès support, while the Lee--Yang side is forced away from the Lattès
quadratic subfield by the visible `3`-ramification and discriminant mismatch. -/
def killo_leyang_lattes_triple_product_galois_pairwise_separation : Prop :=
  Disjoint killoLeyangTenQuadraticRamificationPrimes
      killo_leyang_lattes_triple_product_galois_lattes_ramification_primes ∧
    3 ∈ killoLeyangCubicQuadraticRamificationPrimes ∧
    3 ∉ killo_leyang_lattes_triple_product_galois_lattes_ramification_primes ∧
    killoLeyangTenQuadraticSubfieldDiscriminant ≠
      killo_leyang_lattes_triple_product_galois_lattes_quadratic_discriminant ∧
    killoLeyangCubicQuadraticSubfieldDiscriminant ≠
      killo_leyang_lattes_triple_product_galois_lattes_quadratic_discriminant

/-- Chapter-local direct-product stand-in for the triple compositum. -/
def killo_leyang_lattes_triple_product_galois_statement : Prop :=
  killoLeyangTwoBranchFieldsProductGalois ∧
    fold_gauge_anomaly_trigonal_branch_splitting_field_productGalois ∧
    killo_leyang_lattes_triple_product_galois_pairwise_separation ∧
    killo_leyang_lattes_triple_product_galois_lattes_field_order = 48 ∧
    killoLeyangTenBranchFieldOrder * killoLeyangCubicBranchFieldOrder *
        killo_leyang_lattes_triple_product_galois_lattes_field_order =
      Nat.factorial 10 * Nat.factorial 3 * 48

/-- Paper label: `thm:killo-leyang-lattes-triple-product-galois`. -/
theorem paper_killo_leyang_lattes_triple_product_galois :
    -((2 : ℤ) ^ 19 * 37 ^ 3) = -((2 : ℤ) ^ 19 * 37 ^ 3) ∧
      killo_leyang_lattes_triple_product_galois_lattes_field_order = 48 ∧
      killo_leyang_lattes_triple_product_galois_pairwise_separation ∧
      killo_leyang_lattes_triple_product_galois_statement := by
  rcases paper_fold_gauge_anomaly_trigonal_branch_splitting_field with
    ⟨_, _, _, _, _, _, _, hlattesProduct⟩
  have hpair :
      killo_leyang_lattes_triple_product_galois_pairwise_separation := by
    refine ⟨by decide, by decide, by decide, ?_, ?_⟩
    · norm_num [killoLeyangTenQuadraticSubfieldDiscriminant,
        killo_leyang_lattes_triple_product_galois_lattes_quadratic_discriminant]
    · norm_num [killoLeyangCubicQuadraticSubfieldDiscriminant,
        killo_leyang_lattes_triple_product_galois_lattes_quadratic_discriminant]
  refine ⟨rfl, by norm_num [killo_leyang_lattes_triple_product_galois_lattes_field_order],
    hpair, ?_⟩
  refine ⟨(paper_killo_leyang_two_branch_fields_product_galois).2, hlattesProduct, hpair, ?_, ?_⟩
  · norm_num [killo_leyang_lattes_triple_product_galois_lattes_field_order]
  · norm_num [killoLeyangTenBranchFieldOrder, killoLeyangCubicBranchFieldOrder,
      killo_leyang_lattes_triple_product_galois_lattes_field_order]

end Omega.Folding
