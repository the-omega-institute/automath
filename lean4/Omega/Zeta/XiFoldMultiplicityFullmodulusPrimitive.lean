import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic
import Omega.Core.Fib

namespace Omega.Zeta

/-- The full Fibonacci modulus for the fold-multiplicity profile at scale `m`. -/
def xi_fold_multiplicity_fullmodulus_primitive_modulus (m : ℕ) : ℕ :=
  Nat.fib (m + 2)

/-- The nonvanishing Fibonacci resonance frequency used to detect the full conductor. -/
def xi_fold_multiplicity_fullmodulus_primitive_frequency (m : ℕ) : ℕ :=
  Nat.fib m

/-- Conductor of a Fourier frequency relative to the full Fibonacci modulus. -/
def xi_fold_multiplicity_fullmodulus_primitive_conductor (m k : ℕ) : ℕ :=
  xi_fold_multiplicity_fullmodulus_primitive_modulus m /
    Nat.gcd k (xi_fold_multiplicity_fullmodulus_primitive_modulus m)

/-- A proper quotient descent certificate: the candidate modulus divides the full modulus, is
proper, and every nonzero Fourier frequency has conductor dividing the candidate modulus. -/
def xi_fold_multiplicity_fullmodulus_primitive_proper_quotient_descends
    (m D : ℕ) (fourierCoeff : ℕ → ℤ) : Prop :=
  D ∣ xi_fold_multiplicity_fullmodulus_primitive_modulus m ∧
    D < xi_fold_multiplicity_fullmodulus_primitive_modulus m ∧
      ∀ k, fourierCoeff k ≠ 0 →
        xi_fold_multiplicity_fullmodulus_primitive_conductor m k ∣ D

lemma xi_fold_multiplicity_fullmodulus_primitive_fib_gcd_skip_two (m : ℕ) :
    Nat.gcd (Nat.fib m) (Nat.fib (m + 2)) = 1 := by
  have hcop_succ : Nat.Coprime (Nat.fib m) (Nat.fib (m + 1)) :=
    Nat.fib_coprime_fib_succ m
  have hcop_skip :
      Nat.Coprime (Nat.fib m) (Nat.fib (m + 1) + Nat.fib m) := by
    exact Nat.coprime_add_self_right.mpr hcop_succ
  have hrec : Nat.fib (m + 2) = Nat.fib (m + 1) + Nat.fib m := by
    rw [Nat.fib_add_two, Nat.add_comm]
  simpa [hrec, Nat.Coprime] using hcop_skip

/-- Paper label: `cor:xi-fold-multiplicity-fullmodulus-primitive`.
A nonzero Fourier coefficient at the Fibonacci resonance frequency has full conductor, so the
Fourier-conductor descent criterion rules out every proper divisor modulus. -/
theorem paper_xi_fold_multiplicity_fullmodulus_primitive
    (m D : ℕ) (fourierCoeff : ℕ → ℤ)
    (hnonzero :
      fourierCoeff (xi_fold_multiplicity_fullmodulus_primitive_frequency m) ≠ 0) :
    ¬ xi_fold_multiplicity_fullmodulus_primitive_proper_quotient_descends
      m D fourierCoeff := by
  intro hdesc
  rcases hdesc with ⟨hDdvd, hDlt, hsupport⟩
  have hfull :
      xi_fold_multiplicity_fullmodulus_primitive_modulus m ∣ D := by
    have hcond :=
      hsupport (xi_fold_multiplicity_fullmodulus_primitive_frequency m) hnonzero
    simpa [xi_fold_multiplicity_fullmodulus_primitive_conductor,
      xi_fold_multiplicity_fullmodulus_primitive_frequency,
      xi_fold_multiplicity_fullmodulus_primitive_modulus,
      xi_fold_multiplicity_fullmodulus_primitive_fib_gcd_skip_two m] using hcond
  have hEq : D = xi_fold_multiplicity_fullmodulus_primitive_modulus m :=
    Nat.dvd_antisymm hDdvd hfull
  omega

end Omega.Zeta
