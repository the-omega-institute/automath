import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic
import Omega.Zeta.SmithPrefixSufficiency

namespace Omega.Zeta

open scoped BigOperators

/-- Kernel count of the diagonal Smith model modulo `p^k`: each coordinate contributes
`p^(min(e_i, k))`. -/
def xiHankelFinitePrecisionKernelCount {m : ℕ} (p : ℕ) (e : Fin m → ℕ) (k : ℕ) : ℕ :=
  ∏ i, p ^ Nat.min (e i) k

/-- Cokernel count of the same Smith model modulo `p^k`: the `i`-th diagonal coordinate
contributes `p^(k - min(e_i, k))`. -/
def xiHankelFinitePrecisionCokernelCount {m : ℕ} (p : ℕ) (e : Fin m → ℕ) (k : ℕ) : ℕ :=
  ∏ i, p ^ (k - Nat.min (e i) k)

lemma xiHankelFinitePrecisionKernelCount_eq {m : ℕ} (p : ℕ) (e : Fin m → ℕ) (k : ℕ) :
    xiHankelFinitePrecisionKernelCount p e k = p ^ smithPrefixValue e k := by
  simp [xiHankelFinitePrecisionKernelCount, smithPrefixValue, Finset.prod_pow_eq_pow_sum]

lemma xiHankelFinitePrecisionCokernelCount_eq {m : ℕ} (p : ℕ) (e : Fin m → ℕ) (k : ℕ) :
    xiHankelFinitePrecisionCokernelCount p e k = p ^ (m * k - smithPrefixValue e k) := by
  rw [show xiHankelFinitePrecisionCokernelCount p e k = p ^ ∑ i, (k - Nat.min (e i) k) by
    simp [xiHankelFinitePrecisionCokernelCount, Finset.prod_pow_eq_pow_sum]]
  have hsum :
      (∑ i : Fin m, (k - Nat.min (e i) k)) = m * k - smithPrefixValue e k := by
    rw [Finset.sum_tsub_distrib]
    · simp [smithPrefixValue, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    · intro i _
      exact Nat.min_le_right _ _
  simp [hsum]

lemma smithPrefixValue_le_totalWindow {m : ℕ} (e : Fin m → ℕ) (k : ℕ) :
    smithPrefixValue e k ≤ m * k := by
  unfold smithPrefixValue
  calc
    (∑ i, Nat.min (e i) k) ≤ ∑ _i : Fin m, k := by
      refine Finset.sum_le_sum ?_
      intro i _
      exact Nat.min_le_right _ _
    _ = m * k := by simp

/-- Paper label: `thm:xi-hankel-finite-precision-potential-smith-kernel-coker`. For the diagonal
Smith model modulo `p^k`, the kernel and cokernel counts are the expected power laws controlled by
the Smith-prefix valuation, the kernel stabilizes once `k` exceeds the top exponent, and the
kernel-cokernel product recovers the ambient cardinality `p^(mk)`. -/
theorem paper_xi_hankel_finite_precision_potential_smith_kernel_coker {m : ℕ}
    (p : ℕ) (e : Fin m → ℕ) (k : ℕ) :
    xiHankelFinitePrecisionKernelCount p e k = p ^ smithPrefixValue e k ∧
      xiHankelFinitePrecisionCokernelCount p e k = p ^ (m * k - smithPrefixValue e k) ∧
      (smithPrefixTop e ≤ k →
        xiHankelFinitePrecisionKernelCount p e k = p ^ ∑ i, e i) ∧
      xiHankelFinitePrecisionKernelCount p e k *
          xiHankelFinitePrecisionCokernelCount p e k = p ^ (m * k) := by
  refine ⟨xiHankelFinitePrecisionKernelCount_eq p e k, xiHankelFinitePrecisionCokernelCount_eq p e k,
    ?_, ?_⟩
  · intro htop
    rw [xiHankelFinitePrecisionKernelCount_eq, smithPrefixValue_eq_total_of_le_top e k htop]
  · rw [xiHankelFinitePrecisionKernelCount_eq, xiHankelFinitePrecisionCokernelCount_eq, ← pow_add]
    have hle : smithPrefixValue e k ≤ m * k := smithPrefixValue_le_totalWindow e k
    have hsum : smithPrefixValue e k + (m * k - smithPrefixValue e k) = m * k := by omega
    simp [hsum]

end Omega.Zeta
