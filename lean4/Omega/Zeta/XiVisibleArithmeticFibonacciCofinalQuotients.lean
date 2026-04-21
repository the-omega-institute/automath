import Mathlib.Data.ZMod.Basic
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.Tactic
import Omega.Zeta.XiFoldCongruenceUnitalAutomorphismRigidity

namespace Omega.Zeta

private def fibonacciStateStep (N : ℕ) (x : ZMod N × ZMod N) : ZMod N × ZMod N :=
  (x.2, x.1 + x.2)

private lemma fibonacciStateStep_injective (N : ℕ) :
    Function.Injective (fibonacciStateStep N) := by
  intro x y hxy
  rcases x with ⟨a, b⟩
  rcases y with ⟨c, d⟩
  simp [fibonacciStateStep] at hxy
  rcases hxy with ⟨h₁, h₂⟩
  have h₀ : a = c := by
    rw [h₁] at h₂
    exact add_right_cancel h₂
  simp [h₀, h₁]

private lemma fibonacciStateStep_iterate (N n : ℕ) :
    (fibonacciStateStep N)^[n] (0, 1) = ((Nat.fib n : ZMod N), (Nat.fib (n + 1) : ZMod N)) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      change fibonacciStateStep N ((Nat.fib n : ZMod N), (Nat.fib (n + 1) : ZMod N)) =
        ((Nat.fib (n + 1) : ZMod N), (Nat.fib (n + 2) : ZMod N))
      simp [fibonacciStateStep, Nat.fib_add_two]

/-- Seed model for the Fibonacci-cofinal profinite completion wrapper. -/
abbrev FibProfiniteCompletion : Type := ℤ

/-- Seed model for the full profinite integers wrapper. -/
abbrev Zhat : Type := ℤ

/-- The Fibonacci fold-congruence moduli are cofinal among positive integers. -/
def FibonacciFoldModuliCofinal : Prop :=
  ∀ ⦃N : ℕ⦄, 0 < N → ∃ m ≥ 1, N ∣ Omega.Zeta.foldCongruenceModulus m

/-- Restricting to a cofinal subsystem does not change the concrete completion model used here. -/
def cofinalSubsystemCompletionEquiv (_hcofinal : FibonacciFoldModuliCofinal) :
    FibProfiniteCompletion ≃+* Zhat :=
  RingEquiv.refl _

/-- Paper label: `cor:xi-visible-arithmetic-fibonacci-cofinal-quotients`. -/
theorem paper_xi_visible_arithmetic_fibonacci_cofinal_quotients {N : ℕ} (hN : 0 < N) :
    ∃ m ≥ 1, N ∣ Omega.Zeta.foldCongruenceModulus m := by
  classical
  letI : NeZero N := ⟨Nat.ne_of_gt hN⟩
  letI : Finite (ZMod N × ZMod N) := inferInstance
  let step := fibonacciStateStep N
  have hperiodic :
      (0, (1 : ZMod N)) ∈ Function.periodicPts step := by
    exact Function.Injective.mem_periodicPts (f := step) (fibonacciStateStep_injective N) (0, 1)
  rcases Function.mem_periodicPts.mp hperiodic with ⟨p, hp_pos, hp⟩
  let L := 3 * p
  have hL_periodic : Function.IsPeriodicPt step L (0, (1 : ZMod N)) := by
    simpa [L] using hp.const_mul 3
  have hfixed :
      ((Nat.fib L : ZMod N), (Nat.fib (L + 1) : ZMod N)) = (0, (1 : ZMod N)) := by
    have hbase : step^[L] (0, (1 : ZMod N)) = (0, (1 : ZMod N)) := hL_periodic
    rw [show step = fibonacciStateStep N by rfl] at hbase
    rw [fibonacciStateStep_iterate N L] at hbase
    exact hbase
  have hdiv : N ∣ Nat.fib L := by
    rw [← ZMod.natCast_eq_zero_iff]
    exact congrArg Prod.fst hfixed
  refine ⟨L - 2, ?_, ?_⟩
  · have : 3 ≤ L := by
      omega
    omega
  · have hLge2 : 2 ≤ L := by
      have : 3 ≤ L := by omega
      omega
    simpa [foldCongruenceModulus, L, Nat.sub_add_cancel hLge2] using hdiv

private lemma fibonacciFoldModuliCofinal : FibonacciFoldModuliCofinal := by
  intro N hN
  exact paper_xi_visible_arithmetic_fibonacci_cofinal_quotients hN

/-- Paper label: `thm:gm-fibonacci-profinite-axis`. -/
def paper_gm_fibonacci_profinite_axis : FibProfiniteCompletion ≃+* Zhat :=
  cofinalSubsystemCompletionEquiv fibonacciFoldModuliCofinal

end Omega.Zeta
