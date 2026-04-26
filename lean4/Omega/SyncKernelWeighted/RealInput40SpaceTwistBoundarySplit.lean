import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Omega.SyncKernelWeighted.RealInput40PrimeArtinSplitting
import Omega.SyncKernelWeighted.RealInput40PrimitiveLucasSimplified

namespace Omega.SyncKernelWeighted

open scoped ArithmeticFunction.Moebius BigOperators

/-- The boundary correction left over from the low-order Möbius inversion. -/
def real_input_40_space_twist_boundary_split_boundaryCorrection (n : ℕ) : ℚ :=
  if n = 1 then -1 else if n = 2 then 2 else 0

/-- Wrapper statement combining the prime-Artin parity split, the simplified primitive Lucas
formula on the stable range `n > 2`, and the fact that the residual boundary correction is
supported only at `n = 1, 2`. -/
def real_input_40_space_twist_boundary_split_statement : Prop :=
  (∀ u v : ℤ, ∀ n : ℕ,
    realInput40PrimeArtinOrbitCount u v n =
      if n % 2 = 1 then
        realInput40TensorTrace u v n - realInput40SignedTrace u v n
      else if n % 4 = 0 then
        realInput40TensorTrace u v n + realInput40SignedTrace u v n
      else
        realInput40ArtinTrace u v n + (u ^ (n / 2) + v ^ (n / 2))) ∧
    (∀ n : ℕ, 2 < n →
      (1 / (n : ℚ)) * Finset.sum n.divisors
          (fun d => (ArithmeticFunction.moebius d : ℚ) * (realInput40TraceSequence (n / d) : ℚ)) =
        (1 / (n : ℚ)) * Finset.sum n.divisors
          (fun d => (ArithmeticFunction.moebius d : ℚ) *
            ((Omega.lucasNum (2 * (n / d)) : ℚ) +
              (-1 : ℚ) ^ (n / d) * (Omega.lucasNum (n / d) : ℚ))) ∧
        real_input_40_space_twist_boundary_split_boundaryCorrection n = 0) ∧
    real_input_40_space_twist_boundary_split_boundaryCorrection 1 = -1 ∧
    real_input_40_space_twist_boundary_split_boundaryCorrection 2 = 2 ∧
    ∀ n : ℕ,
      real_input_40_space_twist_boundary_split_boundaryCorrection n ≠ 0 → n = 1 ∨ n = 2

/-- Paper label: `cor:real-input-40-space-twist-boundary-split`. -/
theorem paper_real_input_40_space_twist_boundary_split :
    real_input_40_space_twist_boundary_split_statement := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro u v n
    exact paper_real_input_40_prime_artin_splitting u v n
  · intro n hn
    refine ⟨paper_real_input_40_primitive_lucas_simplified n hn, ?_⟩
    simp [real_input_40_space_twist_boundary_split_boundaryCorrection, Nat.ne_of_gt hn,
      Nat.ne_of_gt (lt_trans (by decide : 1 < 2) hn)]
  · simp [real_input_40_space_twist_boundary_split_boundaryCorrection]
  · simp [real_input_40_space_twist_boundary_split_boundaryCorrection]
  · intro n hn
    by_cases h1 : n = 1
    · exact Or.inl h1
    by_cases h2 : n = 2
    · exact Or.inr h2
    exfalso
    exact hn (by simp [real_input_40_space_twist_boundary_split_boundaryCorrection, h1, h2])

end Omega.SyncKernelWeighted
