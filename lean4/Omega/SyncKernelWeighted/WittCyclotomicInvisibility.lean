import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

/-- Same-stage cyclotomic invisibility for a Witt tower: every `p`-th root-of-unity twist agrees
with the untwisted stage modulo `p^k`. -/
def wittCyclotomicInvisibility {U : Type*} [Monoid U] (p : ℕ) (a : U → ℕ → ℤ) : Prop :=
  ∀ u, u ^ p = 1 → ∀ k, 1 ≤ k → ((p ^ k : ℤ) ∣ a u k - a 1 k)

/-- Paper label: `cor:witt-cyclotomic-invisibility`.
If both the twisted and untwisted stages are congruent modulo `p^k` to the same previous base
stage, then their difference is also divisible by `p^k`. -/
theorem paper_witt_cyclotomic_invisibility {U : Type*} [Monoid U] (p : ℕ) (_hp : Nat.Prime p)
    (a : U → ℕ → ℤ)
    (htower : ∀ u, u ^ p = 1 → ∀ k, 1 ≤ k → ((p ^ k : ℤ) ∣ a u k - a 1 (k - 1)))
    (hbase : ∀ k, 1 ≤ k → ((p ^ k : ℤ) ∣ a 1 k - a 1 (k - 1))) :
    wittCyclotomicInvisibility p a := by
  intro u hu k hk
  have huStage : ((p ^ k : ℤ) ∣ a u k - a 1 (k - 1)) := htower u hu k hk
  have hbaseStage : ((p ^ k : ℤ) ∣ a 1 k - a 1 (k - 1)) := hbase k hk
  have hsplit :
      a u k - a 1 k = (a u k - a 1 (k - 1)) - (a 1 k - a 1 (k - 1)) := by
    ring
  rw [hsplit]
  exact Int.dvd_sub huStage hbaseStage

end Omega.SyncKernelWeighted
