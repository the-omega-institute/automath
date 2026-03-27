import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Nat.Fib.Basic

namespace Omega

open Polynomial

/-- Fibonacci polynomials: F_0(x)=0, F_1(x)=1, F_{n+2}(x)=F_{n+1}(x)+x·F_n(x).
    def:pom-fibonacci-polynomial -/
noncomputable def fibPoly : Nat → Polynomial ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => fibPoly (n + 1) + X * fibPoly n

/-- def:pom-fibonacci-polynomial-simp-zero -/
@[simp] theorem fibPoly_zero : fibPoly 0 = 0 := rfl
@[simp] theorem fibPoly_one : fibPoly 1 = 1 := rfl
@[simp] theorem fibPoly_succ_succ (n : Nat) :
    fibPoly (n + 2) = fibPoly (n + 1) + X * fibPoly n := rfl

/-- fibPoly evaluated at t=1 gives the standard Fibonacci sequence.
    def:pom-fibonacci-polynomial-eval-one -/
theorem fibPoly_eval_one : ∀ n : Nat, (fibPoly n).eval 1 = (Nat.fib n : ℤ)
  | 0 => by simp [fibPoly]
  | 1 => by simp [fibPoly]
  | n + 2 => by
    simp only [fibPoly_succ_succ, eval_add, eval_mul, eval_X, one_mul,
      fibPoly_eval_one (n + 1), fibPoly_eval_one n]
    have := Nat.fib_add_two (n := n)
    push_cast [this]; ring

/-- Path independent set polynomial: I_ℓ(x) = F_{ℓ+2}(x).
    thm:pom-path-indset-poly-closed-def -/
noncomputable def pathIndSetPoly (ℓ : Nat) : Polynomial ℤ := fibPoly (ℓ + 2)

/-- pathIndSetPoly at t=1 gives Fibonacci numbers.
    thm:pom-path-indset-poly-closed-eval-one -/
theorem pathIndSetPoly_eval_one (ℓ : Nat) :
    (pathIndSetPoly ℓ).eval 1 = (Nat.fib (ℓ + 2) : ℤ) :=
  fibPoly_eval_one (ℓ + 2)

/-- fibPoly 2 = 1 + X.
    def:pom-fibonacci-polynomial-two -/
theorem fibPoly_two : fibPoly 2 = 1 := by simp [fibPoly]
/-- def:pom-fibonacci-polynomial-three -/
theorem fibPoly_three : fibPoly 3 = 1 + X := by simp [fibPoly, mul_one]

/-- fibPoly evaluated at t=0: F_0(0)=0, F_n(0)=1 for n ≥ 1.
    thm:pom-fibonacci-polynomial-eval-zero -/
theorem fibPoly_eval_zero : ∀ n : Nat, (fibPoly n).eval 0 = if n = 0 then 0 else 1
  | 0 => by simp [fibPoly]
  | 1 => by simp [fibPoly]
  | n + 2 => by
    simp only [fibPoly_succ_succ, eval_add, eval_mul, eval_X, zero_mul, add_zero,
      fibPoly_eval_zero (n + 1), show n + 2 ≠ 0 from by omega, show n + 1 ≠ 0 from by omega,
      ite_false]

/-- pathIndSetPoly evaluated at t=0 is always 1.
    thm:pom-path-indset-poly-eval-zero -/
theorem pathIndSetPoly_eval_zero (ℓ : Nat) : (pathIndSetPoly ℓ).eval 0 = 1 := by
  simp [pathIndSetPoly, fibPoly_eval_zero, show ℓ + 2 ≠ 0 from by omega]

/-- pathIndSetPoly recurrence: I_{ℓ+2}(x) = I_{ℓ+1}(x) + x · I_ℓ(x).
    thm:pom-path-indset-poly-recurrence -/
theorem pathIndSetPoly_recurrence (ℓ : Nat) :
    pathIndSetPoly (ℓ + 2) = pathIndSetPoly (ℓ + 1) + X * pathIndSetPoly ℓ := by
  simp [pathIndSetPoly, fibPoly_succ_succ]

/-- Paper: pathIndSetPoly(0) = 1.
    thm:pom-path-indset-poly-closed -/
theorem pathIndSetPoly_zero_val : pathIndSetPoly 0 = 1 := fibPoly_two

/-- Paper: pathIndSetPoly(1) = 1 + X.
    thm:pom-path-indset-poly-closed -/
theorem pathIndSetPoly_one_val : pathIndSetPoly 1 = 1 + Polynomial.X := fibPoly_three

end Omega
