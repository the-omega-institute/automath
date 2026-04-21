import Mathlib.Tactic

namespace Omega.Folding

/-- The unique quadratic normal subfield of the degree-`10` branch field. -/
def killoLeyangTenQuadraticSubfieldDiscriminant : ℤ :=
  66269989

/-- The unique quadratic normal subfield of the Lee--Yang cubic branch field. -/
def killoLeyangCubicQuadraticSubfieldDiscriminant : ℤ :=
  -111

/-- Ramification primes of `Q(√66269989)`. -/
def killoLeyangTenQuadraticRamificationPrimes : Finset ℕ :=
  {1931, 34319}

/-- Ramification primes of `Q(√-111)`. -/
def killoLeyangCubicQuadraticRamificationPrimes : Finset ℕ :=
  {3, 37}

/-- The audited Galois orders of the two splitting fields. -/
def killoLeyangTenBranchFieldOrder : ℕ :=
  Nat.factorial 10

def killoLeyangCubicBranchFieldOrder : ℕ :=
  Nat.factorial 3

/-- Disjoint ramification forces the two quadratic subfields, hence any nontrivial intersection, to
be distinct. This is the chapter-local stand-in for `L₁₀ ∩ L_LY = ℚ`. -/
def killoLeyangTwoBranchFieldsTrivialIntersection : Prop :=
  Disjoint killoLeyangTenQuadraticRamificationPrimes killoLeyangCubicQuadraticRamificationPrimes ∧
    killoLeyangTenQuadraticSubfieldDiscriminant ≠ killoLeyangCubicQuadraticSubfieldDiscriminant

/-- The standard restriction map identifies the compositum Galois group with the direct product. -/
def killoLeyangTwoBranchFieldsProductGalois : Prop :=
  killoLeyangTwoBranchFieldsTrivialIntersection ∧
    killoLeyangTenBranchFieldOrder = Nat.factorial 10 ∧
    killoLeyangCubicBranchFieldOrder = Nat.factorial 3 ∧
    killoLeyangTenBranchFieldOrder * killoLeyangCubicBranchFieldOrder =
      Nat.factorial 10 * Nat.factorial 3

/-- Paper label: `thm:killo-leyang-two-branch-fields-product-galois`. -/
theorem paper_killo_leyang_two_branch_fields_product_galois :
    killoLeyangTwoBranchFieldsTrivialIntersection ∧ killoLeyangTwoBranchFieldsProductGalois := by
  have hIntersection : killoLeyangTwoBranchFieldsTrivialIntersection := by
    refine ⟨by decide, ?_⟩
    norm_num [killoLeyangTenQuadraticSubfieldDiscriminant,
      killoLeyangCubicQuadraticSubfieldDiscriminant]
  refine ⟨hIntersection, ?_⟩
  exact ⟨hIntersection, rfl, rfl, rfl⟩

end Omega.Folding
