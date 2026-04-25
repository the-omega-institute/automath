import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.Perm.Finite
import Mathlib.Tactic

namespace Omega.Zeta

/-- The order indices appearing in the Fibonacci torsion union. -/
def xi_time_part62da_fibonacci_torsion_saturates_circle_fibonacci_orders : Set ℕ :=
  {N | ∃ m : ℕ, 1 ≤ m ∧ N ∣ Nat.fib (m + 2)}

/-- The order indices of finite torsion on the circle. -/
def xi_time_part62da_fibonacci_torsion_saturates_circle_torsion_orders : Set ℕ :=
  {N | 0 < N}

/-- The Fibonacci step on pairs modulo `N`. -/
def xi_time_part62da_fibonacci_torsion_saturates_circle_step (N : ℕ) :
    (ZMod N × ZMod N) ≃ (ZMod N × ZMod N) where
  toFun p := (p.2, p.1 + p.2)
  invFun p := (p.2 - p.1, p.1)
  left_inv := by
    intro p
    ext <;> simp [sub_eq_add_neg, add_assoc]
  right_inv := by
    intro p
    ext <;> simp [sub_eq_add_neg, add_comm]

lemma xi_time_part62da_fibonacci_torsion_saturates_circle_step_iterate
    (N k : ℕ) :
    ((xi_time_part62da_fibonacci_torsion_saturates_circle_step N)^[k]) (0, 1) =
      ((Nat.fib k : ZMod N), (Nat.fib (k + 1) : ZMod N)) := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      rw [ih]
      simp [xi_time_part62da_fibonacci_torsion_saturates_circle_step, Nat.fib_add_two,
        add_comm, add_left_comm]

lemma xi_time_part62da_fibonacci_torsion_saturates_circle_fibonacci_cofinal
    {N : ℕ} (hN : 0 < N) :
    ∃ m : ℕ, 1 ≤ m ∧ N ∣ Nat.fib (m + 2) := by
  haveI : NeZero N := ⟨Nat.ne_of_gt hN⟩
  let e := xi_time_part62da_fibonacci_torsion_saturates_circle_step N
  haveI : Fintype ((ZMod N × ZMod N) ≃ (ZMod N × ZMod N)) := inferInstance
  haveI : Finite ((ZMod N × ZMod N) ≃ (ZMod N × ZMod N)) :=
    Fintype.finite (inferInstance : Fintype ((ZMod N × ZMod N) ≃ (ZMod N × ZMod N)))
  let k := orderOf e
  have hkpos : 0 < k := by
    exact orderOf_pos e
  have hpow_point : (e^[k]) (0, 1) = (0, 1) := by
    have hpow : e ^ k = 1 := by
      simp [k]
    have happly : (e ^ k) (0, 1) = (1 : (ZMod N × ZMod N) ≃ (ZMod N × ZMod N)) (0, 1) := by
      rw [hpow]
    simpa only [Equiv.Perm.coe_pow, Equiv.Perm.coe_one, id_eq] using happly
  have hstate := xi_time_part62da_fibonacci_torsion_saturates_circle_step_iterate N k
  have hfib_zero : (Nat.fib k : ZMod N) = 0 := by
    have hpair : ((Nat.fib k : ZMod N), (Nat.fib (k + 1) : ZMod N)) = (0, 1) :=
      hstate.symm.trans hpow_point
    exact congrArg Prod.fst hpair
  have hNdvd_fibk : N ∣ Nat.fib k :=
    (ZMod.natCast_eq_zero_iff (Nat.fib k) N).mp hfib_zero
  refine ⟨3 * k - 2, ?_, ?_⟩
  · omega
  · have hk_dvd : k ∣ 3 * k := dvd_mul_left k 3
    have hfib_dvd : Nat.fib k ∣ Nat.fib (3 * k) := Nat.fib_dvd k (3 * k) hk_dvd
    have hsum : 3 * k - 2 + 2 = 3 * k := by omega
    simpa [hsum] using hNdvd_fibk.trans hfib_dvd

/-- Concrete set equality for the Fibonacci torsion union: the positive orders that occur in
some Fibonacci level are exactly all positive finite torsion orders. -/
def xi_time_part62da_fibonacci_torsion_saturates_circle_statement : Prop :=
  xi_time_part62da_fibonacci_torsion_saturates_circle_fibonacci_orders =
    xi_time_part62da_fibonacci_torsion_saturates_circle_torsion_orders

/-- Paper label: `thm:xi-time-part62da-fibonacci-torsion-saturates-circle`. -/
theorem paper_xi_time_part62da_fibonacci_torsion_saturates_circle :
    xi_time_part62da_fibonacci_torsion_saturates_circle_statement := by
  ext N
  constructor
  · rintro ⟨m, hm, hdiv⟩
    have hfib_pos : 0 < Nat.fib (m + 2) := by
      rw [Nat.fib_pos]
      omega
    by_contra hnot
    have hN0 : N = 0 := Nat.eq_zero_of_not_pos hnot
    subst N
    rcases hdiv with ⟨c, hc⟩
    have hc0 : Nat.fib (m + 2) = 0 := by
      rw [hc]
      simp
    exact (Nat.ne_of_gt hfib_pos) hc0
  · intro hN
    exact xi_time_part62da_fibonacci_torsion_saturates_circle_fibonacci_cofinal hN

end Omega.Zeta
