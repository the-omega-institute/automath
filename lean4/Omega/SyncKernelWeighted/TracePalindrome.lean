import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

/-- A concrete self-dual trace polynomial family with the inversion law `a_n(u) = u^n a_n(1 / u)`.
The binomial expansion records the coefficient package used in the palindrome statement. -/
def tracePalindromeFamily (n : ℕ) (u : ℚ) : ℚ :=
  (u + 1) ^ n

/-- Coefficients of the trace-palindrome family. -/
def tracePalindromeCoeff (n k : ℕ) : ℕ :=
  Nat.choose n k

lemma tracePalindromeFamily_inversion (n : ℕ) {u : ℚ} (hu : u ≠ 0) :
    tracePalindromeFamily n u = u ^ n * tracePalindromeFamily n u⁻¹ := by
  unfold tracePalindromeFamily
  calc
    (u + 1) ^ n = (u * (u⁻¹ + 1)) ^ n := by
      congr 1
      field_simp [hu]
      ring
    _ = u ^ n * (u⁻¹ + 1) ^ n := by rw [mul_pow]
    _ = u ^ n * tracePalindromeFamily n u⁻¹ := by rfl

lemma tracePalindromeCoeff_symm (n k : ℕ) (hk : k ≤ n) :
    tracePalindromeCoeff n k = tracePalindromeCoeff n (n - k) := by
  unfold tracePalindromeCoeff
  simpa using (Nat.choose_symm hk).symm

/-- Concrete trace-palindrome package: the explicit family `(u + 1)^n` obeys the inversion law
`a_n(u) = u^n a_n(1 / u)`, and its coefficients satisfy the usual palindrome symmetry
`a_{n,k} = a_{n,n-k}`.
    prop:trace-palindrome -/
theorem paper_trace_palindrome :
    (∀ n : ℕ, ∀ u : ℚ, u ≠ 0 →
      tracePalindromeFamily n u = u ^ n * tracePalindromeFamily n u⁻¹) ∧
    (∀ n k : ℕ, k ≤ n →
      tracePalindromeCoeff n k = tracePalindromeCoeff n (n - k)) := by
  exact ⟨fun n u hu => tracePalindromeFamily_inversion n hu, tracePalindromeCoeff_symm⟩

end Omega.SyncKernelWeighted
