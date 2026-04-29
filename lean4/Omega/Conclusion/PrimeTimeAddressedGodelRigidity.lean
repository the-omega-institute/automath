import Mathlib.Tactic
import Omega.Conclusion.PrimeShiftPhaseVisibleTwoGenerator

open Omega.GroupUnification

/-- Time-addressed Gödel rigidity, stated in the existing finite-support prime-register model. -/
def conclusion_prime_time_addressed_godel_rigidity_statement : Prop :=
  (∀ {A : Type*} [AddCommGroup A] (f : Omega.Conclusion.PrimeShiftLedger → A),
    f (0, 0) = 0 →
      (∀ x y, f (Omega.Conclusion.primeShiftMul x y) = f x + f y) →
        ∃! g : ℕ × ℕ → A,
          Omega.Conclusion.NatPairAdditive g ∧
            ∀ x : Omega.Conclusion.PrimeShiftLedger,
              f x = g (Omega.Conclusion.primeShiftPi x)) ∧
    (∀ t : ℕ, primeRegisterShift (primeBasis t) = primeBasis (t + 1)) ∧
      (∀ r : PrimeRegisterObject,
        Omega.Conclusion.primeShiftOmega (primeRegisterShift r) =
          Omega.Conclusion.primeShiftOmega r)

/-- The time shift sends each basis address to the next basis address. -/
private theorem conclusion_prime_time_addressed_godel_rigidity_shift_basis (t : ℕ) :
    primeRegisterShift (primeBasis t) = primeBasis (t + 1) := by
  exact primeRegisterShift_basis t

/-- Shift compatibility extends from basis vectors to all finitely supported exponent vectors. -/
private theorem conclusion_prime_time_addressed_godel_rigidity_shift_omega
    (r : PrimeRegisterObject) :
    Omega.Conclusion.primeShiftOmega (primeRegisterShift r) =
      Omega.Conclusion.primeShiftOmega r := by
  let omegaHom : PrimeRegisterObject →+ ℕ :=
    { toFun := Omega.Conclusion.primeShiftOmega
      map_zero' := Omega.Conclusion.primeShiftOmega_zero
      map_add' := Omega.Conclusion.primeShiftOmega_add }
  have hcomp : AddMonoidHom.comp omegaHom primeRegisterShift = omegaHom := by
    apply Finsupp.addHom_ext
    intro t n
    simp [omegaHom, Omega.Conclusion.primeShiftOmega, primeBasis]
  exact congrArg (fun h : PrimeRegisterObject →+ ℕ => h r) hcomp

/-- Paper label: `thm:conclusion-prime-time-addressed-godel-rigidity`. -/
theorem paper_conclusion_prime_time_addressed_godel_rigidity :
    conclusion_prime_time_addressed_godel_rigidity_statement := by
  refine ⟨?_, conclusion_prime_time_addressed_godel_rigidity_shift_basis,
    conclusion_prime_time_addressed_godel_rigidity_shift_omega⟩
  intro A _ f hzero hmul
  exact Omega.Conclusion.paper_conclusion_prime_shift_phase_visible_two_generator f hzero hmul
