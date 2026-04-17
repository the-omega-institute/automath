import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete chapter-local model of nonzero endomorphisms of the `S = {2, 3}` localized solenoid:
the two valuations of the exterior numerator. -/
structure LocalizedSolenoidEndomorphism where
  v2 : ℕ
  v3 : ℕ

/-- Composition adds the `2`-adic and `3`-adic exterior valuations. -/
def localizedSolenoidComp (f g : LocalizedSolenoidEndomorphism) : LocalizedSolenoidEndomorphism :=
  ⟨f.v2 + g.v2, f.v3 + g.v3⟩

/-- Exterior numerator degree formula for the localized-solenoid endomorphism. -/
def localizedSolenoidExteriorNumeratorDegree (f : LocalizedSolenoidEndomorphism) : ℕ :=
  2 ^ f.v2 * 3 ^ f.v3

/-- Positive covering degrees realized by the localized-solenoid endomorphisms. -/
def localizedSolenoidDegreeOccurs (n : ℕ) : Prop :=
  ∃ f : LocalizedSolenoidEndomorphism, localizedSolenoidExteriorNumeratorDegree f = n

/-- Classification of the positive degree image by the exterior numerator formula. -/
def localizedSolenoidDegreeImageClassification : Prop :=
  ∀ n : ℕ, localizedSolenoidDegreeOccurs n ↔ 0 < n ∧ ∃ a b : ℕ, n = 2 ^ a * 3 ^ b

/-- Multiplicativity of the covering degree under composition. -/
def localizedSolenoidDegreeMultiplicative : Prop :=
  ∀ f g : LocalizedSolenoidEndomorphism,
    localizedSolenoidExteriorNumeratorDegree (localizedSolenoidComp f g) =
      localizedSolenoidExteriorNumeratorDegree f * localizedSolenoidExteriorNumeratorDegree g

/-- Positive covering degrees of nonzero localized-solenoid endomorphisms are exactly the
`S`-exterior numerator degrees `2^a 3^b`, and these degrees multiply under composition.
    cor:xi-localized-solenoid-nonzero-endomorphism-degree-semigroup -/
theorem paper_xi_localized_solenoid_nonzero_endomorphism_degree_semigroup :
    localizedSolenoidDegreeImageClassification ∧ localizedSolenoidDegreeMultiplicative := by
  constructor
  · intro n
    constructor
    · rintro ⟨f, rfl⟩
      refine ⟨Nat.mul_pos (pow_pos (by decide) _) (pow_pos (by decide) _), f.v2, f.v3, rfl⟩
    · rintro ⟨hn, a, b, rfl⟩
      exact ⟨⟨a, b⟩, rfl⟩
  · intro f g
    simp [localizedSolenoidExteriorNumeratorDegree, localizedSolenoidComp, pow_add,
      Nat.mul_assoc, Nat.mul_left_comm]

end Omega.Zeta
