import Mathlib.Tactic
import Omega.POM.ResonanceQ16Q17DedekindFactorization
import Omega.POM.ResonanceQ16Q17LinearlyDisjoint

namespace Omega.POM

/-- Order of the symmetric group on the thirteen roots. -/
def pom_resonance_q16_q17_simultaneous_irreducible_chebotarev_s13_order : ℕ :=
  Nat.factorial 13

/-- Number of thirteen-cycles in `S₁₃`, namely `(13 - 1)!`. -/
def pom_resonance_q16_q17_simultaneous_irreducible_chebotarev_s13_cycle_count : ℕ :=
  Nat.factorial 12

/-- Proportion of thirteen-cycles in `S₁₃`. -/
def pom_resonance_q16_q17_simultaneous_irreducible_chebotarev_single_density : ℚ :=
  pom_resonance_q16_q17_simultaneous_irreducible_chebotarev_s13_cycle_count /
    pom_resonance_q16_q17_simultaneous_irreducible_chebotarev_s13_order

/-- Order of the linearly-disjoint product Galois group. -/
def pom_resonance_q16_q17_simultaneous_irreducible_chebotarev_product_order : ℕ :=
  pom_resonance_q16_q17_simultaneous_irreducible_chebotarev_s13_order *
    pom_resonance_q16_q17_simultaneous_irreducible_chebotarev_s13_order

/-- Number of product Frobenius classes whose two projections are thirteen-cycles. -/
def pom_resonance_q16_q17_simultaneous_irreducible_chebotarev_product_cycle_count :
    ℕ :=
  pom_resonance_q16_q17_simultaneous_irreducible_chebotarev_s13_cycle_count *
    pom_resonance_q16_q17_simultaneous_irreducible_chebotarev_s13_cycle_count

/-- Chebotarev density of simultaneous irreducibility in the product group. -/
def pom_resonance_q16_q17_simultaneous_irreducible_chebotarev_density : ℚ :=
  pom_resonance_q16_q17_simultaneous_irreducible_chebotarev_product_cycle_count /
    pom_resonance_q16_q17_simultaneous_irreducible_chebotarev_product_order

/-- Explicit prime witness for simultaneous irreducibility. -/
def pom_resonance_q16_q17_simultaneous_irreducible_chebotarev_prime_witness : ℕ :=
  4003

/-- Recorded factor-degree pattern for `P₁₆ mod 4003`. -/
def pom_resonance_q16_q17_simultaneous_irreducible_chebotarev_witness_pattern16 :
    List ℕ :=
  [13]

/-- Recorded factor-degree pattern for `P₁₇ mod 4003`. -/
def pom_resonance_q16_q17_simultaneous_irreducible_chebotarev_witness_pattern17 :
    List ℕ :=
  [13]

/-- Statement package for the simultaneous-irreducibility Chebotarev certificate. -/
def pom_resonance_q16_q17_simultaneous_irreducible_chebotarev_statement : Prop :=
  (pom_resonance_q16_q17_linearly_disjoint_intersection_trivial ∧
      pom_resonance_q16_q17_linearly_disjoint_galois_product) ∧
    pom_resonance_q16_q17_dedekind_factorization_statement ∧
    pom_resonance_q16_q17_simultaneous_irreducible_chebotarev_s13_cycle_count =
      Nat.factorial 12 ∧
    pom_resonance_q16_q17_simultaneous_irreducible_chebotarev_s13_order =
      Nat.factorial 13 ∧
    pom_resonance_q16_q17_simultaneous_irreducible_chebotarev_single_density =
      1 / 13 ∧
    pom_resonance_q16_q17_simultaneous_irreducible_chebotarev_product_order =
      Nat.factorial 13 * Nat.factorial 13 ∧
    pom_resonance_q16_q17_simultaneous_irreducible_chebotarev_product_cycle_count =
      Nat.factorial 12 * Nat.factorial 12 ∧
    pom_resonance_q16_q17_simultaneous_irreducible_chebotarev_density = 1 / 169 ∧
    (1 : ℚ) / 13 ^ 2 = 1 / 169 ∧
    pom_resonance_q16_q17_simultaneous_irreducible_chebotarev_prime_witness = 4003 ∧
    Nat.Prime pom_resonance_q16_q17_simultaneous_irreducible_chebotarev_prime_witness ∧
    pom_resonance_q16_q17_simultaneous_irreducible_chebotarev_witness_pattern16 = [13] ∧
    pom_resonance_q16_q17_simultaneous_irreducible_chebotarev_witness_pattern17 = [13]

/-- Paper label:
`thm:pom-resonance-q16-q17-simultaneous-irreducible-chebotarev`. -/
theorem paper_pom_resonance_q16_q17_simultaneous_irreducible_chebotarev :
    pom_resonance_q16_q17_simultaneous_irreducible_chebotarev_statement := by
  unfold pom_resonance_q16_q17_simultaneous_irreducible_chebotarev_statement
  refine ⟨paper_pom_resonance_q16_q17_linearly_disjoint,
    paper_pom_resonance_q16_q17_dedekind_factorization, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · norm_num [pom_resonance_q16_q17_simultaneous_irreducible_chebotarev_single_density,
      pom_resonance_q16_q17_simultaneous_irreducible_chebotarev_s13_cycle_count,
      pom_resonance_q16_q17_simultaneous_irreducible_chebotarev_s13_order]
  · rfl
  · rfl
  · norm_num [pom_resonance_q16_q17_simultaneous_irreducible_chebotarev_density,
      pom_resonance_q16_q17_simultaneous_irreducible_chebotarev_product_cycle_count,
      pom_resonance_q16_q17_simultaneous_irreducible_chebotarev_product_order,
      pom_resonance_q16_q17_simultaneous_irreducible_chebotarev_s13_cycle_count,
      pom_resonance_q16_q17_simultaneous_irreducible_chebotarev_s13_order]
  · norm_num
  · rfl
  · norm_num [pom_resonance_q16_q17_simultaneous_irreducible_chebotarev_prime_witness]
  · rfl
  · rfl

end Omega.POM
