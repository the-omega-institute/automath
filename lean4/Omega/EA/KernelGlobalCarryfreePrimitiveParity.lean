import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic
import Omega.EA.KernelGlobalCarryfreeSpectralTrichotomy
import Omega.Folding.ShiftDynamics

namespace Omega.EA

open scoped ArithmeticFunction.Moebius
open scoped BigOperators

/-- Möbius-inversion wrapper that extracts primitive orbit counts from a concrete trace sequence. -/
def primitiveOrbitCountFromTrace (trace : ℕ → ℤ) : ℕ → ℤ
  | 0 => 0
  | n + 1 =>
      (∑ d ∈ Nat.divisors (n + 1), ArithmeticFunction.moebius d * trace ((n + 1) / d)) / (n + 1)

/-- The `K9` carry-free trace channel, written as the `7`-eigenvalue contribution on the global
branch. -/
def kernelGlobalCarryfreeTraceK9 (m : ℕ) : ℤ :=
  (7 : ℤ) ^ (4 * m)

/-- The `K13` carry-free trace channel, written as the `3`-eigenvalue contribution on the global
branch. -/
def kernelGlobalCarryfreeTraceK13 (m : ℕ) : ℤ :=
  (3 : ℤ) ^ (2 * m)

/-- The `K21` carry-free trace channel, written as the square of the Lucas trace of the golden
branch before splitting off the parity correction. -/
def kernelGlobalCarryfreeTraceK21 (m : ℕ) : ℤ :=
  (Omega.lucasNum m : ℤ) ^ 2

/-- Primitive orbit counts of the `K9` global carry-free branch. -/
def kernelGlobalCarryfreePrimitiveK9 : ℕ → ℤ :=
  primitiveOrbitCountFromTrace kernelGlobalCarryfreeTraceK9

/-- Primitive orbit counts of the `K13` global carry-free branch. -/
def kernelGlobalCarryfreePrimitiveK13 : ℕ → ℤ :=
  primitiveOrbitCountFromTrace kernelGlobalCarryfreeTraceK13

/-- Primitive orbit counts of the `K21` global carry-free branch. -/
def kernelGlobalCarryfreePrimitiveK21 : ℕ → ℤ :=
  primitiveOrbitCountFromTrace kernelGlobalCarryfreeTraceK21

private lemma kernelGlobalCarryfreeTraceK9_closed (m : ℕ) :
    kernelGlobalCarryfreeTraceK9 m = (2401 : ℤ) ^ m := by
  rw [kernelGlobalCarryfreeTraceK9, pow_mul]
  norm_num

private lemma kernelGlobalCarryfreeTraceK13_closed (m : ℕ) :
    kernelGlobalCarryfreeTraceK13 m = (9 : ℤ) ^ m := by
  rw [kernelGlobalCarryfreeTraceK13, pow_mul]
  norm_num

private lemma kernelGlobalCarryfreeTraceK21_closed (m : ℕ) :
    kernelGlobalCarryfreeTraceK21 m = (Omega.lucasNum (2 * m) : ℤ) + 2 * (-1 : ℤ) ^ m := by
  unfold kernelGlobalCarryfreeTraceK21
  have hdouble := Omega.lucasNum_double_uncond m
  linarith

/-- The global carry-free primitive orbit counts are the Möbius inverses of the three explicit
trace channels; the `K21` branch is the unique one with a parity correction term.
    thm:kernel-global-carryfree-primitive-parity -/
theorem paper_kernel_global_carryfree_primitive_parity (n : ℕ) :
    kernelGlobalCarryfreePrimitiveK9 n =
        primitiveOrbitCountFromTrace (fun m => (2401 : ℤ) ^ m) n ∧
      kernelGlobalCarryfreePrimitiveK13 n =
        primitiveOrbitCountFromTrace (fun m => (9 : ℤ) ^ m) n ∧
      kernelGlobalCarryfreePrimitiveK21 n =
        primitiveOrbitCountFromTrace
          (fun m => (Omega.lucasNum (2 * m) : ℤ) + 2 * (-1 : ℤ) ^ m) n := by
  cases n with
  | zero =>
      simp [kernelGlobalCarryfreePrimitiveK9, kernelGlobalCarryfreePrimitiveK13,
        kernelGlobalCarryfreePrimitiveK21, primitiveOrbitCountFromTrace]
  | succ n =>
      simp [kernelGlobalCarryfreePrimitiveK9, kernelGlobalCarryfreePrimitiveK13,
        kernelGlobalCarryfreePrimitiveK21, primitiveOrbitCountFromTrace,
        kernelGlobalCarryfreeTraceK9_closed, kernelGlobalCarryfreeTraceK13_closed,
        kernelGlobalCarryfreeTraceK21_closed]

end Omega.EA
