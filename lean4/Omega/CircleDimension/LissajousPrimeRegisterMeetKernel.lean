import Mathlib.Data.Nat.Factorization.Basic
import Omega.CircleDimension.LissajousPhaseCirclePrimeLedgerKernel

namespace Omega.CircleDimension

/-- Paper label: `cor:cdim-lissajous-prime-register-meet-kernel`. The phase-circle kernel is the
gcd of the two frequencies, and the same integer is the prime-register meet product recovered
from its factorization. -/
theorem paper_cdim_lissajous_prime_register_meet_kernel
    (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (δ : ℝ) :
    let d := lissajousPrimeLedgerKernel a b
    d = Nat.gcd a b ∧
      d = (Nat.gcd a b).factorization.prod (· ^ ·) ∧
      Nat.Coprime (a / d) (b / d) ∧
      Fintype.card (Fin d) = (Nat.gcd a b).factorization.prod (· ^ ·) := by
  dsimp [lissajousPrimeLedgerKernel]
  have hgcd_ne_zero : Nat.gcd a b ≠ 0 := Nat.ne_of_gt (Nat.gcd_pos_of_pos_left _ ha)
  rcases paper_cdim_lissajous_phase_circle_prime_ledger_kernel a b ha hb δ with
    ⟨hcop, -, -, -, -, hcard⟩
  refine ⟨rfl, ?_, ?_, ?_⟩
  · exact (Nat.factorization_prod_pow_eq_self hgcd_ne_zero).symm
  · simpa using hcop
  · calc
      Fintype.card (Fin (Nat.gcd a b)) = Nat.gcd a b := by simp
      _ = (Nat.gcd a b).factorization.prod (· ^ ·) := by
        rw [Nat.factorization_prod_pow_eq_self hgcd_ne_zero]

end Omega.CircleDimension
