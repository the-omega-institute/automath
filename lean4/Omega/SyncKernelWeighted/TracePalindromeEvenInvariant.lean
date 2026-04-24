import Mathlib.Data.Rat.Defs
import Mathlib.Tactic
import Omega.SyncKernelWeighted.TracePalindrome

namespace Omega.SyncKernelWeighted

/-- Concrete even-degree package for the trace-palindrome normalization. The even degree is
recorded by its half-degree `k`, so the palindromic trace polynomial is `(u + 1)^(2k)`. -/
structure TracePalindromeEvenInvariantData where
  halfDegree : ℕ

namespace TracePalindromeEvenInvariantData

/-- The even degree `n = 2k`. -/
def evenDegree (D : TracePalindromeEvenInvariantData) : ℕ :=
  2 * D.halfDegree

/-- The even-palindrome normalization `u^{-k} a_{2k}(u)`, written in the equivalent
division-free form `u^k a_{2k}(u^{-1})`. -/
def normalizedTrace (D : TracePalindromeEvenInvariantData) (u : ℚ) : ℚ :=
  u ^ D.halfDegree * tracePalindromeFamily D.evenDegree u⁻¹

/-- The inversion-invariant coordinate `t = u + u^{-1}`. -/
def invariantCoordinate (u : ℚ) : ℚ :=
  u + u⁻¹

/-- The descended polynomial in the coordinate `t = u + u^{-1}`. -/
def invariantPolynomial (D : TracePalindromeEvenInvariantData) (t : ℚ) : ℚ :=
  (t + 2) ^ D.halfDegree

/-- The normalized even trace factors through the inversion-invariant coordinate. -/
def descendsToInvariantCoordinate (D : TracePalindromeEvenInvariantData) : Prop :=
  ∀ u : ℚ, u ≠ 0 → D.normalizedTrace u = D.invariantPolynomial (invariantCoordinate u)

/-- The normalized even trace is fixed by `u ↦ u^{-1}`. -/
def fixedByInversion (D : TracePalindromeEvenInvariantData) : Prop :=
  ∀ u : ℚ, u ≠ 0 → D.normalizedTrace u⁻¹ = D.normalizedTrace u

/-- The descended polynomial is the unique decomposition witness on the image of the substitution
`t = u + u^{-1}`. -/
def invariantPolynomialUniqueOnImage (D : TracePalindromeEvenInvariantData) : Prop :=
  ∀ P : ℚ → ℚ,
    (∀ u : ℚ, u ≠ 0 → D.normalizedTrace u = P (invariantCoordinate u)) →
      ∀ t : ℚ, (∃ u : ℚ, u ≠ 0 ∧ invariantCoordinate u = t) → P t = D.invariantPolynomial t

/-- Paper-facing invariant decomposition package for the normalized even palindrome. -/
def hasInvariantDecomposition (D : TracePalindromeEvenInvariantData) : Prop :=
  D.descendsToInvariantCoordinate ∧ D.fixedByInversion ∧ D.invariantPolynomialUniqueOnImage

lemma normalizedTrace_eq_invariant (D : TracePalindromeEvenInvariantData) (u : ℚ) (hu : u ≠ 0) :
    D.normalizedTrace u = D.invariantPolynomial (invariantCoordinate u) := by
  unfold normalizedTrace invariantPolynomial invariantCoordinate evenDegree tracePalindromeFamily
  have hbase : u * (u⁻¹ + 1) ^ 2 = u + u⁻¹ + 2 := by
    field_simp [hu]
    ring
  calc
    u ^ D.halfDegree * (u⁻¹ + 1) ^ (2 * D.halfDegree)
        = u ^ D.halfDegree * ((u⁻¹ + 1) ^ 2) ^ D.halfDegree := by rw [pow_mul]
    _ = (u * (u⁻¹ + 1) ^ 2) ^ D.halfDegree := by rw [← mul_pow]
    _ = (u + u⁻¹ + 2) ^ D.halfDegree := by rw [hbase]
    _ = (u + u⁻¹ + 2) ^ D.halfDegree := rfl

lemma descendsToInvariantCoordinate_true (D : TracePalindromeEvenInvariantData) :
    D.descendsToInvariantCoordinate := by
  intro u hu
  exact D.normalizedTrace_eq_invariant u hu

lemma fixedByInversion_true (D : TracePalindromeEvenInvariantData) :
    D.fixedByInversion := by
  intro u hu
  rw [D.normalizedTrace_eq_invariant u⁻¹ (inv_ne_zero hu), D.normalizedTrace_eq_invariant u hu]
  simp [invariantCoordinate, add_comm]

lemma invariantPolynomialUniqueOnImage_true (D : TracePalindromeEvenInvariantData) :
    D.invariantPolynomialUniqueOnImage := by
  intro P hP t ht
  rcases ht with ⟨u, hu, rfl⟩
  rw [← hP u hu, D.normalizedTrace_eq_invariant u hu]

end TracePalindromeEvenInvariantData

open TracePalindromeEvenInvariantData

/-- Paper label: `lem:trace-palindrome-even-invariant`. -/
theorem paper_trace_palindrome_even_invariant (D : TracePalindromeEvenInvariantData) :
    D.hasInvariantDecomposition := by
  let _ := paper_trace_palindrome
  exact ⟨D.descendsToInvariantCoordinate_true, D.fixedByInversion_true,
    D.invariantPolynomialUniqueOnImage_true⟩

end Omega.SyncKernelWeighted
