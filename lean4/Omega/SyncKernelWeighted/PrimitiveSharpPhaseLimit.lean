import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

open scoped BigOperators

/-- The Möbius-type primitive sum after the Perron contribution has been removed termwise. -/
def primitiveSharpMobiusSum (μ : ℕ → ℝ) (centeredTrace : ℕ → ℝ) (n : ℕ) : ℝ :=
  Finset.sum n.divisors fun d => μ d * centeredTrace (n / d)

/-- The `d = 1` main phase contribution. -/
def primitiveSharpMainPhase (centeredTrace : ℕ → ℝ) (n : ℕ) : ℝ :=
  centeredTrace n

/-- The divisor-tail remainder coming from `d ≥ 2`. -/
def primitiveSharpRemainder (μ : ℕ → ℝ) (centeredTrace : ℕ → ℝ) (n : ℕ) : ℝ :=
  Finset.sum (n.divisors.erase 1) fun d => μ d * centeredTrace (n / d)

/-- Paper-facing statement: isolate the `d = 1` phase and bound the `d ≥ 2` divisor tail by a
`Λ^n` remainder with an explicit divisor-count prefactor. -/
def PrimitiveSharpPhaseLimitStatement (μ : ℕ → ℝ) (centeredTrace : ℕ → ℝ)
    (Λ : ℝ) (n : ℕ) : Prop :=
  primitiveSharpMobiusSum μ centeredTrace n =
      primitiveSharpMainPhase centeredTrace n + primitiveSharpRemainder μ centeredTrace n ∧
    |primitiveSharpRemainder μ centeredTrace n| ≤ ((n.divisors.erase 1).card : ℝ) * Λ ^ n

/-- Paper label: `prop:primitive-sharp-phase-limit`. -/
theorem paper_primitive_sharp_phase_limit (μ : ℕ → ℝ) (centeredTrace : ℕ → ℝ) (Λ : ℝ) (n : ℕ)
    (hn : 0 < n) (hΛ : 0 ≤ Λ) (hμ1 : μ 1 = 1)
    (hμtail : ∀ d ∈ n.divisors.erase 1, |μ d| ≤ 1)
    (htraceTail : ∀ d ∈ n.divisors.erase 1, |centeredTrace (n / d)| ≤ Λ ^ n) :
    PrimitiveSharpPhaseLimitStatement μ centeredTrace Λ n := by
  refine ⟨?_, ?_⟩
  · have h1 : 1 ∈ n.divisors := by
      simp [Nat.mem_divisors, hn.ne']
    have hsplit :
        primitiveSharpMobiusSum μ centeredTrace n =
          primitiveSharpRemainder μ centeredTrace n + μ 1 * centeredTrace (n / 1) := by
      unfold primitiveSharpMobiusSum primitiveSharpRemainder
      simpa [add_comm, add_left_comm, add_assoc] using
        (Finset.sum_erase_add (s := n.divisors)
          (f := fun d => μ d * centeredTrace (n / d)) h1).symm
    simpa [primitiveSharpMainPhase, hμ1, add_comm] using hsplit
  · calc
      |primitiveSharpRemainder μ centeredTrace n|
          = |Finset.sum (n.divisors.erase 1) (fun d => μ d * centeredTrace (n / d))| := rfl
      _ ≤ Finset.sum (n.divisors.erase 1) (fun d => |μ d * centeredTrace (n / d)|) := by
        simpa [primitiveSharpRemainder] using
          (Finset.abs_sum_le_sum_abs (s := n.divisors.erase 1)
            (f := fun d => μ d * centeredTrace (n / d)))
      _ ≤ Finset.sum (n.divisors.erase 1) fun _ => Λ ^ n := by
        refine Finset.sum_le_sum ?_
        intro d hd
        rw [abs_mul]
        have hμabs : 0 ≤ |μ d| := abs_nonneg (μ d)
        have htraceAbs : 0 ≤ |centeredTrace (n / d)| := abs_nonneg (centeredTrace (n / d))
        have hΛn : 0 ≤ Λ ^ n := pow_nonneg hΛ n
        nlinarith [hμtail d hd, htraceTail d hd]
      _ = ((n.divisors.erase 1).card : ℝ) * Λ ^ n := by
        simp
