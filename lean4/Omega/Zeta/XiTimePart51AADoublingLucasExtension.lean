import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic
import Omega.Core.Fib
import Omega.Folding.ShiftDynamics

namespace Omega.Zeta

/-- Paper-facing Lucas extension package for the doubled Fibonacci modulus. The quotient
`F_(2n) / F_n` is the Lucas factor `L_n`, and the only possible common divisor between `F_n`
and `L_n` is the parity obstruction coming from `F_n`. -/
def xi_time_part51aa_doubling_lucas_extension_spec (m : ℕ) : Prop :=
  let n := m + 1
  Nat.fib (2 * n) = Nat.fib n * Omega.lucasNum n ∧
    Nat.fib (2 * n) / Nat.fib n = Omega.lucasNum n ∧
    Nat.gcd (Omega.lucasNum n) (Nat.fib n) = Nat.gcd (Nat.fib n) 2 ∧
    Nat.gcd (Omega.lucasNum n) (Nat.fib n) = (if 3 ∣ n then 2 else 1) ∧
    (Nat.Coprime (Nat.fib n) (Omega.lucasNum n) ↔ ¬ 3 ∣ n)

/-- Paper label: `thm:xi-time-part51aa-doubling-lucas-extension`. -/
theorem paper_xi_time_part51aa_doubling_lucas_extension (m : ℕ) :
    xi_time_part51aa_doubling_lucas_extension_spec m := by
  dsimp [xi_time_part51aa_doubling_lucas_extension_spec]
  let n := m + 1
  have hn : 1 ≤ n := by
    dsimp [n]
    omega
  have hdouble : Nat.fib (2 * n) = Nat.fib n * Omega.lucasNum n := by
    simpa [Nat.mul_comm] using Omega.fib_double_eq_mul_lucas n
  have hfib_pos : 0 < Nat.fib n := Nat.fib_pos.mpr hn
  have hquot : Nat.fib (2 * n) / Nat.fib n = Omega.lucasNum n := by
    calc
      Nat.fib (2 * n) / Nat.fib n = (Nat.fib n * Omega.lucasNum n) / Nat.fib n := by rw [hdouble]
      _ = Omega.lucasNum n := by
        simpa [Nat.mul_comm] using (Nat.mul_div_right (Omega.lucasNum n) hfib_pos)
  have hgcd_exact : Nat.gcd (Omega.lucasNum n) (Nat.fib n) = if 3 ∣ n then 2 else 1 := by
    simpa using Omega.lucasNum_fib_gcd_eq n
  have hgcd_fib_two : Nat.gcd (Nat.fib n) 2 = if 3 ∣ n then 2 else 1 := by
    by_cases h3 : 3 ∣ n
    · have h_even : 2 ∣ Nat.fib n := (Omega.fib_even_iff_three_dvd n).2 h3
      rw [if_pos h3]
      exact Nat.gcd_eq_right_iff_dvd.mpr h_even
    · have h_not_even : ¬ 2 ∣ Nat.fib n := (Omega.fib_even_iff_three_dvd n).not.mpr h3
      rw [if_neg h3]
      have hle : Nat.gcd (Nat.fib n) 2 ≤ 2 := Nat.le_of_dvd (by decide : 0 < 2) (Nat.gcd_dvd_right _ _)
      have hne_zero : Nat.gcd (Nat.fib n) 2 ≠ 0 := by
        exact Nat.gcd_ne_zero_right (by decide : 2 ≠ 0)
      have hpos : 0 < Nat.gcd (Nat.fib n) 2 := Nat.pos_of_ne_zero hne_zero
      have hne : Nat.gcd (Nat.fib n) 2 ≠ 2 := by
        intro hg
        exact h_not_even (hg ▸ Nat.gcd_dvd_left (Nat.fib n) 2)
      omega
  have hgcd_bridge : Nat.gcd (Omega.lucasNum n) (Nat.fib n) = Nat.gcd (Nat.fib n) 2 := by
    rw [hgcd_exact, hgcd_fib_two]
  have hcoprime : Nat.Coprime (Nat.fib n) (Omega.lucasNum n) ↔ ¬ 3 ∣ n := by
    rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm, hgcd_exact]
    by_cases h3 : 3 ∣ n <;> simp [h3]
  exact ⟨hdouble, hquot, hgcd_bridge, hgcd_exact, hcoprime⟩

end Omega.Zeta
