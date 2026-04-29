import Mathlib.Data.List.Permutation
import Mathlib.Tactic
import Omega.CircleDimension.DerivedChainArithmeticMedianUniqueMinimizer

namespace Omega.CircleDimension

/-- The concrete divisibility interval cut out by the squarefree support difference between `1`
and `30`. -/
def derivedChainArithmeticInterval : Finset ℕ := {1, 2, 3, 5, 6, 10, 15, 30}

/-- The support rank of the squarefree ratio `30 / 1 = 2 * 3 * 5`. -/
def derivedChainArithmeticRank : ℕ := 3

/-- The Boolean-cube model of the interval. -/
def derivedChainArithmeticBooleanCubeStructure : Prop :=
  Nonempty ({n : ℕ // n ∈ derivedChainArithmeticInterval} ≃ (Fin derivedChainArithmeticRank → Bool))

/-- An explicit equivalence exists because the interval has eight elements, matching the `3`-cube.
-/
noncomputable def derivedChainArithmeticBooleanCubeEquiv :
    {n : ℕ // n ∈ derivedChainArithmeticInterval} ≃ (Fin derivedChainArithmeticRank → Bool) :=
  Classical.choice <| Fintype.card_eq.mp (by
    simp [derivedChainArithmeticInterval, derivedChainArithmeticRank])

/-- Prime orders generating monotone geodesics from `1` to `30`. -/
def derivedChainArithmeticSupportOrderings : List (List ℕ) := [2, 3, 5].permutations

/-- Multiplying the support primes in a chosen order traces a shortest divisibility geodesic. -/
def derivedChainArithmeticGeodesicOfOrdering : List ℕ → List ℕ
  | [a, b, c] => [1, a, a * b, a * b * c]
  | _ => []

/-- The shortest geodesics are exactly the monotone chains obtained from the support orderings. -/
def derivedChainArithmeticShortestGeodesics : List (List ℕ) :=
  derivedChainArithmeticSupportOrderings.map derivedChainArithmeticGeodesicOfOrdering

/-- Every shortest geodesic in the concrete interval is indexed by a permutation of the support. -/
def derivedChainArithmeticShortestGeodesicsArePermutations : Prop :=
  ∀ γ, γ ∈ derivedChainArithmeticShortestGeodesics ↔
    ∃ σ ∈ derivedChainArithmeticSupportOrderings, γ = derivedChainArithmeticGeodesicOfOrdering σ

/-- Number of shortest monotone geodesics from `1` to `30`. -/
def derivedChainArithmeticShortestGeodesicCount : ℕ :=
  derivedChainArithmeticShortestGeodesics.length

/-- The squarefree divisibility interval between `1` and `30` is a Boolean `3`-cube, its shortest
monotone geodesics are exactly the support permutations, and there are `3!` of them.
    cor:derived-chain-arithmetic-boolean-interval-geodesics -/
theorem paper_derived_chain_arithmetic_boolean_interval_geodesics :
    derivedChainArithmeticBooleanCubeStructure ∧
      derivedChainArithmeticShortestGeodesicsArePermutations ∧
      derivedChainArithmeticShortestGeodesicCount = Nat.factorial derivedChainArithmeticRank := by
  refine ⟨⟨derivedChainArithmeticBooleanCubeEquiv⟩, ?_, ?_⟩
  · intro γ
    constructor
    · intro hγ
      simp [derivedChainArithmeticShortestGeodesics, derivedChainArithmeticSupportOrderings] at hγ
      rcases hγ with ⟨σ, hσ, hEq⟩
      refine ⟨σ, ?_, hEq.symm⟩
      simpa [derivedChainArithmeticSupportOrderings] using hσ
    · rintro ⟨σ, hσ, rfl⟩
      simp [derivedChainArithmeticShortestGeodesics]
      refine ⟨σ, ?_, rfl⟩
      simpa [derivedChainArithmeticSupportOrderings] using hσ
  · calc
      derivedChainArithmeticShortestGeodesicCount =
          derivedChainArithmeticSupportOrderings.length := by
            simp [derivedChainArithmeticShortestGeodesicCount,
              derivedChainArithmeticShortestGeodesics]
      _ = Nat.factorial derivedChainArithmeticRank := by
            simpa [derivedChainArithmeticSupportOrderings, derivedChainArithmeticRank] using
              (List.length_permutations [2, 3, 5])

end Omega.CircleDimension
