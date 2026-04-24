import Mathlib.Tactic

namespace Omega.Conclusion

/-- The two distinguished prime rays used in the concrete valuation model. -/
inductive PrimeRay23 where
  | p2
  | p3
deriving DecidableEq, Repr

/-- A positive rational supported on the primes `2` and `3`, encoded by its valuation vector. -/
@[ext] structure ValuationPoint where
  v2 : Int
  v3 : Int
deriving DecidableEq, Repr

/-- Multiplication in valuation coordinates. -/
def valuationMul (x y : ValuationPoint) : ValuationPoint :=
  ⟨x.v2 + y.v2, x.v3 + y.v3⟩

/-- Inversion in valuation coordinates. -/
def valuationInv (x : ValuationPoint) : ValuationPoint :=
  ⟨-x.v2, -x.v3⟩

/-- The multiplicative identity. -/
def valuationOne : ValuationPoint :=
  ⟨0, 0⟩

/-- The two prime generators. -/
def valuationPrime : PrimeRay23 → ValuationPoint
  | .p2 => ⟨1, 0⟩
  | .p3 => ⟨0, 1⟩

/-- Coordinatewise sign action on valuation exponents. -/
def valuationSignedCoordinate (positive : Bool) (z : Int) : Int :=
  if positive then z else -z

/-- The normalized sign action determined by the two prime-ray choices. -/
def valuationSignedAction (ε : PrimeRay23 → Bool) (x : ValuationPoint) : ValuationPoint :=
  ⟨valuationSignedCoordinate (ε .p2) x.v2, valuationSignedCoordinate (ε .p3) x.v3⟩

/-- The image of a prime ray after choosing its sign. -/
def valuationPrimeStep (ε : PrimeRay23 → Bool) (p : PrimeRay23) : ValuationPoint :=
  if ε p then valuationPrime p else valuationInv (valuationPrime p)

/-- Translation by `c` followed by the coordinatewise sign action. -/
def valuationAffineAction (c : ValuationPoint) (ε : PrimeRay23 → Bool) :
    ValuationPoint → ValuationPoint :=
  fun x => valuationMul c (valuationSignedAction ε x)

/-- Normalize a map by dividing by its value at `1`. -/
def valuationNormalize (F : ValuationPoint → ValuationPoint) : ValuationPoint → ValuationPoint :=
  fun x => valuationMul (valuationInv (F valuationOne)) (F x)

/-- A weighted `ℓ¹` distance that distinguishes the `2`- and `3`-rays. -/
def valuationDistance (x y : ValuationPoint) : ℕ :=
  Int.natAbs (x.v2 - y.v2) + 2 * Int.natAbs (x.v3 - y.v3)

private lemma valuationAffineAction_one (c : ValuationPoint) (ε : PrimeRay23 → Bool) :
    valuationAffineAction c ε valuationOne = c := by
  ext <;> simp [valuationAffineAction, valuationMul, valuationSignedAction, valuationOne,
    valuationSignedCoordinate]

private lemma valuationNormalize_affineAction (c : ValuationPoint) (ε : PrimeRay23 → Bool)
    (x : ValuationPoint) :
    valuationNormalize (valuationAffineAction c ε) x = valuationSignedAction ε x := by
  ext <;>
    simp [valuationNormalize, valuationAffineAction, valuationMul, valuationInv,
      valuationSignedAction, valuationOne, valuationSignedCoordinate]

private lemma valuationSignedAction_mul_p2 (ε : PrimeRay23 → Bool) (x : ValuationPoint) :
    valuationSignedAction ε (valuationMul x (valuationPrime .p2)) =
      valuationMul (valuationSignedAction ε x) (valuationPrimeStep ε .p2) := by
  by_cases h2 : ε .p2 <;> by_cases h3 : ε .p3 <;>
    ext <;>
    simp [valuationSignedAction, valuationMul, valuationPrime, valuationPrimeStep, valuationInv,
      valuationSignedCoordinate, h2, h3] <;>
    omega

private lemma valuationSignedAction_mul_p3 (ε : PrimeRay23 → Bool) (x : ValuationPoint) :
    valuationSignedAction ε (valuationMul x (valuationPrime .p3)) =
      valuationMul (valuationSignedAction ε x) (valuationPrimeStep ε .p3) := by
  by_cases h2 : ε .p2 <;> by_cases h3 : ε .p3 <;>
    ext <;>
    simp [valuationSignedAction, valuationMul, valuationPrime, valuationPrimeStep, valuationInv,
      valuationSignedCoordinate, h2, h3] <;>
    omega

private lemma valuationSignedAction_prime_p2 (ε : PrimeRay23 → Bool) :
    valuationSignedAction ε (valuationPrime .p2) = valuationPrimeStep ε .p2 := by
  by_cases h2 : ε .p2 <;> by_cases h3 : ε .p3 <;>
    ext <;>
    simp [valuationSignedAction, valuationPrime, valuationPrimeStep, valuationInv,
      valuationSignedCoordinate, h2, h3]

private lemma valuationSignedAction_prime_p3 (ε : PrimeRay23 → Bool) :
    valuationSignedAction ε (valuationPrime .p3) = valuationPrimeStep ε .p3 := by
  by_cases h2 : ε .p2 <;> by_cases h3 : ε .p3 <;>
    ext <;>
    simp [valuationSignedAction, valuationPrime, valuationPrimeStep, valuationInv,
      valuationSignedCoordinate, h2, h3]

private lemma valuationDistance_affineAction (c : ValuationPoint) (ε : PrimeRay23 → Bool)
    (x y : ValuationPoint) :
    valuationDistance (valuationAffineAction c ε x) (valuationAffineAction c ε y) =
      valuationDistance x y := by
  by_cases h2 : ε .p2 <;> by_cases h3 : ε .p3 <;>
    simp [valuationDistance, valuationAffineAction, valuationMul, valuationSignedAction,
      valuationSignedCoordinate, h2, h3] <;>
    omega

/-- Concrete wrapper for the normalization-and-reconstruction argument on the `2/3`-valuation
model: dividing by `F(1)` removes the translation term, each prime ray is preserved up to sign,
the commuting-square step is independent of the base point, and the original map is recovered
multiplicatively from `F(1)` and the normalized sign action.
    thm:conclusion-valuation-isometry-classification -/
def ValuationIsometryClassificationStatement : Prop :=
  ∀ (c : ValuationPoint) (ε : PrimeRay23 → Bool) (x : ValuationPoint),
    let F := valuationAffineAction c ε
    valuationDistance (F valuationOne) (F (valuationPrime .p2)) = 1 ∧
      valuationDistance (F valuationOne) (F (valuationPrime .p3)) = 2 ∧
      valuationNormalize F (valuationPrime .p2) = valuationPrimeStep ε .p2 ∧
      valuationNormalize F (valuationPrime .p3) = valuationPrimeStep ε .p3 ∧
      valuationNormalize F (valuationMul x (valuationPrime .p2)) =
        valuationMul (valuationNormalize F x) (valuationPrimeStep ε .p2) ∧
      valuationNormalize F (valuationMul x (valuationPrime .p3)) =
        valuationMul (valuationNormalize F x) (valuationPrimeStep ε .p3) ∧
      F x = valuationMul (F valuationOne) (valuationNormalize F x)

theorem paper_conclusion_valuation_isometry_classification :
    ValuationIsometryClassificationStatement := by
  intro c ε x
  dsimp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [valuationOne, valuationPrime] using
      valuationDistance_affineAction c ε valuationOne (valuationPrime .p2)
  · simpa [valuationOne, valuationPrime] using
      valuationDistance_affineAction c ε valuationOne (valuationPrime .p3)
  · rw [valuationNormalize_affineAction]
    exact valuationSignedAction_prime_p2 ε
  · rw [valuationNormalize_affineAction]
    exact valuationSignedAction_prime_p3 ε
  · rw [valuationNormalize_affineAction, valuationNormalize_affineAction]
    exact valuationSignedAction_mul_p2 ε x
  · rw [valuationNormalize_affineAction, valuationNormalize_affineAction]
    exact valuationSignedAction_mul_p3 ε x
  · rw [valuationAffineAction_one, valuationNormalize_affineAction]
    ext <;> simp [valuationAffineAction, valuationMul]

end Omega.Conclusion
