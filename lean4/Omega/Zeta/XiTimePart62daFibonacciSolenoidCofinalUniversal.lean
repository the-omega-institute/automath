import Mathlib.Data.ZMod.Basic
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.Tactic

namespace Omega.Zeta

private def xi_time_part62da_fibonacci_solenoid_cofinal_universal_state_step
    (N : ℕ) (x : ZMod N × ZMod N) : ZMod N × ZMod N :=
  (x.2, x.1 + x.2)

private lemma xi_time_part62da_fibonacci_solenoid_cofinal_universal_state_step_injective
    (N : ℕ) :
    Function.Injective
      (xi_time_part62da_fibonacci_solenoid_cofinal_universal_state_step N) := by
  intro x y hxy
  rcases x with ⟨a, b⟩
  rcases y with ⟨c, d⟩
  simp [xi_time_part62da_fibonacci_solenoid_cofinal_universal_state_step] at hxy
  rcases hxy with ⟨h₁, h₂⟩
  have h₀ : a = c := by
    rw [h₁] at h₂
    exact add_right_cancel h₂
  simp [h₀, h₁]

private lemma xi_time_part62da_fibonacci_solenoid_cofinal_universal_state_step_iterate
    (N n : ℕ) :
    (xi_time_part62da_fibonacci_solenoid_cofinal_universal_state_step N)^[n] (0, 1) =
      ((Nat.fib n : ZMod N), (Nat.fib (n + 1) : ZMod N)) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      change
        xi_time_part62da_fibonacci_solenoid_cofinal_universal_state_step N
            ((Nat.fib n : ZMod N), (Nat.fib (n + 1) : ZMod N)) =
          ((Nat.fib (n + 1) : ZMod N), (Nat.fib (n + 2) : ZMod N))
      simp [xi_time_part62da_fibonacci_solenoid_cofinal_universal_state_step,
        Nat.fib_add_two]

/-- Paper label: `thm:xi-time-part62da-fibonacci-solenoid-cofinal-universal`. -/
theorem paper_xi_time_part62da_fibonacci_solenoid_cofinal_universal :
    ∀ N : Nat, 0 < N → ∃ m : Nat, 1 ≤ m ∧ N ∣ Nat.fib (m + 2) := by
  intro N hN
  classical
  letI : NeZero N := ⟨Nat.ne_of_gt hN⟩
  letI : Finite (ZMod N × ZMod N) := inferInstance
  let step := xi_time_part62da_fibonacci_solenoid_cofinal_universal_state_step N
  have hperiodic :
      (0, (1 : ZMod N)) ∈ Function.periodicPts step := by
    exact Function.Injective.mem_periodicPts (f := step)
      (xi_time_part62da_fibonacci_solenoid_cofinal_universal_state_step_injective N) (0, 1)
  rcases Function.mem_periodicPts.mp hperiodic with ⟨p, hp_pos, hp⟩
  let L := 3 * p
  have hL_periodic : Function.IsPeriodicPt step L (0, (1 : ZMod N)) := by
    simpa [L] using hp.const_mul 3
  have hfixed :
      ((Nat.fib L : ZMod N), (Nat.fib (L + 1) : ZMod N)) = (0, (1 : ZMod N)) := by
    have hbase : step^[L] (0, (1 : ZMod N)) = (0, (1 : ZMod N)) := hL_periodic
    rw [show step = xi_time_part62da_fibonacci_solenoid_cofinal_universal_state_step N by
      rfl] at hbase
    rw [xi_time_part62da_fibonacci_solenoid_cofinal_universal_state_step_iterate N L] at hbase
    exact hbase
  have hdiv : N ∣ Nat.fib L := by
    rw [← ZMod.natCast_eq_zero_iff]
    exact congrArg Prod.fst hfixed
  refine ⟨L - 2, ?_, ?_⟩
  · have hL_ge_three : 3 ≤ L := by
      omega
    omega
  · have hL_ge_two : 2 ≤ L := by
      have hL_ge_three : 3 ≤ L := by
        omega
      omega
    simpa [Nat.sub_add_cancel hL_ge_two] using hdiv

end Omega.Zeta
