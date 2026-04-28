import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `prop:conclusion-serrin-wulff-ray-eventual-centerless-gauge`. -/
theorem paper_conclusion_serrin_wulff_ray_eventual_centerless_gauge
    (m Fm Nm qm am : ℕ) (d : Fin Fm → ℕ) (centerlessGauge : Prop)
    (hm : 6 ≤ m) (hF : Fm = Nat.fib (m + 2)) (hN : Nm = 2 ^ m)
    (hdiv : Nm = qm * Fm + am) (ham : am < Fm)
    (hd : ∀ r : Fin Fm, d r = qm + if (r : ℕ) < am then 1 else 0)
    (hCenter : (∀ r : Fin Fm, 3 ≤ d r) → centerlessGauge) :
    3 ≤ qm ∧ (∀ r : Fin Fm, 3 ≤ d r) ∧ centerlessGauge := by
  have hFibShift : ∀ k : ℕ, 3 * Nat.fib (6 + k + 2) ≤ 2 ^ (6 + k) := by
    intro k
    induction k with
    | zero =>
        native_decide
    | succ k ih =>
        have hrec :
            Nat.fib (6 + Nat.succ k + 2) =
              Nat.fib (6 + k + 1) + Nat.fib (6 + k + 2) := by
          rw [show 6 + Nat.succ k + 2 = (6 + k + 1) + 2 by omega, Nat.fib_add_two]
        have hmono : Nat.fib (6 + k + 1) ≤ Nat.fib (6 + k + 2) := by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            (Nat.fib_le_fib_succ : Nat.fib (6 + k + 1) ≤ Nat.fib (6 + k + 1 + 1))
        have hsum :
            3 * (Nat.fib (6 + k + 1) + Nat.fib (6 + k + 2)) ≤
              2 * (3 * Nat.fib (6 + k + 2)) := by
          nlinarith
        calc
          3 * Nat.fib (6 + Nat.succ k + 2)
              = 3 * (Nat.fib (6 + k + 1) + Nat.fib (6 + k + 2)) := by rw [hrec]
          _ ≤ 2 * (3 * Nat.fib (6 + k + 2)) := hsum
          _ ≤ 2 * 2 ^ (6 + k) := Nat.mul_le_mul_left 2 ih
          _ = 2 ^ (6 + Nat.succ k) := by
            rw [show 6 + Nat.succ k = 6 + k + 1 by omega, pow_succ]
            ring
  have hFibBound : 3 * Nat.fib (m + 2) ≤ 2 ^ m := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
    exact hFibShift k
  have hNmLower : 3 * Fm ≤ Nm := by
    simpa [hF, hN] using hFibBound
  have hq : 3 ≤ qm := by
    by_contra hnot
    have hq_le : qm ≤ 2 := by omega
    have hmul : qm * Fm ≤ 2 * Fm := Nat.mul_le_mul_right Fm hq_le
    have hsmall : qm * Fm + am < 3 * Fm := by
      omega
    have hNmSmall : Nm < 3 * Fm := by
      calc
        Nm = qm * Fm + am := hdiv
        _ < 3 * Fm := hsmall
    exact (not_lt_of_ge hNmLower) hNmSmall
  have hdLower : ∀ r : Fin Fm, 3 ≤ d r := by
    intro r
    rw [hd r]
    split <;> omega
  exact ⟨hq, hdLower, hCenter hdLower⟩

end Omega.Conclusion
