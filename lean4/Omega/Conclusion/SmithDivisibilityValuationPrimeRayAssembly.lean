import Mathlib.Tactic
import Omega.Zeta.SmithPrefixSufficiency

namespace Omega.Conclusion

open Omega.Zeta
open scoped BigOperators

/-- Concrete prime-ray Smith data on a finite divisibility lattice. -/
structure conclusion_smith_divisibility_valuation_primeray_assembly_data where
  conclusion_smith_divisibility_valuation_primeray_assembly_rank : ℕ
  conclusion_smith_divisibility_valuation_primeray_assembly_ray :
    Fin conclusion_smith_divisibility_valuation_primeray_assembly_rank → ℕ

namespace conclusion_smith_divisibility_valuation_primeray_assembly_data

/-- The `p`-primary valuation profile assembled from the local prime rays. -/
def conclusion_smith_divisibility_valuation_primeray_assembly_prime_ray_profile
    (D : conclusion_smith_divisibility_valuation_primeray_assembly_data) (p : ℕ) :
    Fin D.conclusion_smith_divisibility_valuation_primeray_assembly_rank → ℕ :=
  fun i =>
    (D.conclusion_smith_divisibility_valuation_primeray_assembly_ray i).factorization p

/-- The divisibility-lattice valuation obtained by assembling the local prime-ray data. -/
def conclusion_smith_divisibility_valuation_primeray_assembly_valuation
    (D : conclusion_smith_divisibility_valuation_primeray_assembly_data) : ℕ → ℕ → ℕ :=
  fun p k =>
    smithPrefixValue
      (D.conclusion_smith_divisibility_valuation_primeray_assembly_prime_ray_profile p) k

/-- The standard Smith kernel-count formula written as the sum of prime-power contributions. -/
def conclusion_smith_divisibility_valuation_primeray_assembly_kernel_log
    (D : conclusion_smith_divisibility_valuation_primeray_assembly_data) : ℕ → ℕ → ℕ :=
  fun p k =>
    ∑ i,
      Nat.min
        ((D.conclusion_smith_divisibility_valuation_primeray_assembly_ray i).factorization p) k

lemma conclusion_smith_divisibility_valuation_primeray_assembly_valuation_eq_kernel_log_at
    (D : conclusion_smith_divisibility_valuation_primeray_assembly_data) (p k : ℕ) :
    D.conclusion_smith_divisibility_valuation_primeray_assembly_valuation p k =
      D.conclusion_smith_divisibility_valuation_primeray_assembly_kernel_log p k := by
  unfold conclusion_smith_divisibility_valuation_primeray_assembly_valuation
    conclusion_smith_divisibility_valuation_primeray_assembly_kernel_log
    conclusion_smith_divisibility_valuation_primeray_assembly_prime_ray_profile
  simp [smithPrefixValue]

end conclusion_smith_divisibility_valuation_primeray_assembly_data

open conclusion_smith_divisibility_valuation_primeray_assembly_data

/-- Paper label: `thm:conclusion-smith-divisibility-valuation-primeray-assembly`.
The prime-ray assembled divisibility valuation is exactly the Smith kernel-count formula obtained
by summing the prime-power factors along the finite Smith profile. -/
theorem paper_conclusion_smith_divisibility_valuation_primeray_assembly
    (D : conclusion_smith_divisibility_valuation_primeray_assembly_data) :
    D.conclusion_smith_divisibility_valuation_primeray_assembly_valuation =
      D.conclusion_smith_divisibility_valuation_primeray_assembly_kernel_log := by
  funext p k
  exact
    conclusion_smith_divisibility_valuation_primeray_assembly_valuation_eq_kernel_log_at D p k

end Omega.Conclusion
