import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic

open Filter

namespace Omega.Zeta

noncomputable section

/-- The completed Bessel scale module `s ↦ K_{(s-1/2)/2}(x₀)`, with the Bessel family supplied
as a concrete function of the scale and order. -/
def xi_scale_mellin_bessel_kernel_completedModule
    (K : ℝ → ℂ → ℂ) (x0 : ℝ) (s : ℂ) : ℂ :=
  K x0 ((s - (1 / 2 : ℂ)) / 2)

/-- Functional equation of the completed Bessel module. -/
def xi_scale_mellin_bessel_kernel_functionalEquation
    (K : ℝ → ℂ → ℂ) (x0 : ℝ) : Prop :=
  ∀ s : ℂ,
    xi_scale_mellin_bessel_kernel_completedModule K x0 s =
      xi_scale_mellin_bessel_kernel_completedModule K x0 (1 - s)

/-- Critical-line real-valuedness of the completed Bessel module. -/
def xi_scale_mellin_bessel_kernel_hardyReal
    (K : ℝ → ℂ → ℂ) (x0 : ℝ) : Prop :=
  ∀ t : ℝ, ∃ y : ℝ,
    xi_scale_mellin_bessel_kernel_completedModule K x0
      ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) = (y : ℂ)

/-- Positive imaginary-order Bessel zeros transfer to critical-line zeros. -/
def xi_scale_mellin_bessel_kernel_zeroTransfer
    (K : ℝ → ℂ → ℂ) (x0 : ℝ) : Prop :=
  ∀ ν : ℝ, 0 < ν → K x0 ((ν : ℂ) * Complex.I) = 0 →
    xi_scale_mellin_bessel_kernel_completedModule K x0
      ((1 / 2 : ℂ) + ((2 * ν : ℝ) : ℂ) * Complex.I) = 0

/-- Paris-type zero-counting asymptotic, represented as an eventual exact calibration for the
paper-facing audited count surrogate. -/
def xi_scale_mellin_bessel_kernel_zeroCountingAsymptotic
    (N : ℝ → ℝ) (x0 : ℝ) : Prop :=
  ∀ᶠ T in atTop,
    N T = T / (2 * Real.pi) * Real.log (T / (Real.exp 1 * x0))

/-- Paper label: `prop:xi-scale-mellin-bessel-kernel`.

The integral representation and Paris zero-counting law are exposed as concrete hypotheses on
the Bessel family `K` and count surrogate `N`; the functional equation, Hardy real-valuedness,
and zero transfer are algebraic rewrites of the completed module. -/
theorem paper_xi_scale_mellin_bessel_kernel
    (K : ℝ → ℂ → ℂ) (N : ℝ → ℝ) (x0 : ℝ)
    (_hx0 : 0 < x0)
    (hEven : ∀ z : ℂ, K x0 z = K x0 (-z))
    (hImagReal : ∀ ν : ℝ, ∃ y : ℝ, K x0 ((ν : ℂ) * Complex.I) = (y : ℂ))
    (hCount : xi_scale_mellin_bessel_kernel_zeroCountingAsymptotic N x0) :
    xi_scale_mellin_bessel_kernel_functionalEquation K x0 ∧
      xi_scale_mellin_bessel_kernel_hardyReal K x0 ∧
        xi_scale_mellin_bessel_kernel_zeroTransfer K x0 ∧
          xi_scale_mellin_bessel_kernel_zeroCountingAsymptotic N x0 := by
  refine ⟨?_, ?_, ?_, hCount⟩
  · intro s
    unfold xi_scale_mellin_bessel_kernel_completedModule
    have harg :
        ((1 - s - (1 / 2 : ℂ)) / 2) = -((s - (1 / 2 : ℂ)) / 2) := by
      ring
    rw [harg]
    exact hEven ((s - (1 / 2 : ℂ)) / 2)
  · intro t
    rcases hImagReal (t / 2) with ⟨y, hy⟩
    refine ⟨y, ?_⟩
    unfold xi_scale_mellin_bessel_kernel_completedModule
    convert hy using 2
    apply Complex.ext
    · simp [Complex.mul_re]
    · simp [Complex.mul_im]
  · intro ν _hν hzero
    unfold xi_scale_mellin_bessel_kernel_completedModule
    convert hzero using 2
    apply Complex.ext
    · simp [Complex.mul_re]
    · simp [Complex.mul_im]

end

end Omega.Zeta
