import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.PNat.Notation
import Mathlib.Tactic

import Omega.UnitCirclePhaseArithmetic.ScaleLinearizationIdentityMultipliers

open scoped BigOperators

namespace Omega.UnitCirclePhaseArithmetic

noncomputable section

/-- The logarithmic depth translation attached to a positive scale. -/
def depthShift (m : ℕ+) : ℝ :=
  Real.log (m : ℝ)

/-- The unit-frequency plane wave on the depth line. -/
def depthWave (ξ : ℝ) (y : ℝ) : ℂ :=
  Complex.exp (((ξ * y : ℝ) : ℂ) * Complex.I)

/-- Finite-support depth translation kernel with Dirichlet-type weights. -/
def depthTranslationKernel (support : Finset ℕ+) (σ : ℕ) (χ : ℕ+ → ℂ) (g : ℝ → ℂ) :
    ℝ → ℂ :=
  fun y => support.sum fun m => χ m / (((m : ℕ) : ℂ) ^ (σ + 1)) * g (y + depthShift m)

/-- The multiplier read off by evaluating the kernel on the plane wave at depth `0`. -/
def finiteDirichletMultiplier (support : Finset ℕ+) (σ : ℕ) (χ : ℕ+ → ℂ) (ξ : ℝ) : ℂ :=
  depthTranslationKernel support σ χ (depthWave ξ) 0

/-- Plane waves diagonalize the finite logarithmic-translation kernel. -/
def fourierDiagonalization (support : Finset ℕ+) (σ : ℕ) (χ : ℕ+ → ℂ) : Prop :=
  ∀ ξ y,
    depthTranslationKernel support σ χ (depthWave ξ) y =
      finiteDirichletMultiplier support σ χ ξ * depthWave ξ y

/-- The multiplier is the corresponding finite Dirichlet series along the logarithmic depth line. -/
def dirichletMultiplierFormula (support : Finset ℕ+) (σ : ℕ) (χ : ℕ+ → ℂ) : Prop :=
  ∀ ξ,
    finiteDirichletMultiplier support σ χ ξ =
      support.sum fun m =>
        χ m / (((m : ℕ) : ℂ) ^ (σ + 1)) * depthWave ξ (depthShift m)

/-- Spectral blocking on a plane wave is exactly vanishing of the multiplier. -/
def spectralBlockingIff (support : Finset ℕ+) (σ : ℕ) (χ : ℕ+ → ℂ) : Prop :=
  ∀ ξ,
    finiteDirichletMultiplier support σ χ ξ = 0 ↔
      ∀ y, depthTranslationKernel support σ χ (depthWave ξ) y = 0

lemma depthWave_add (ξ a y : ℝ) :
    depthWave ξ (a + y) = depthWave ξ a * depthWave ξ y := by
  simp [depthWave, mul_add, Complex.exp_add, mul_comm]

lemma finiteDirichletMultiplier_formula (support : Finset ℕ+) (σ : ℕ) (χ : ℕ+ → ℂ) (ξ : ℝ) :
    finiteDirichletMultiplier support σ χ ξ =
      support.sum fun m =>
        χ m / (((m : ℕ) : ℂ) ^ (σ + 1)) * depthWave ξ (depthShift m) := by
  simp [finiteDirichletMultiplier, depthTranslationKernel]

lemma depthTranslationKernel_on_wave (support : Finset ℕ+) (σ : ℕ) (χ : ℕ+ → ℂ) (ξ y : ℝ) :
    depthTranslationKernel support σ χ (depthWave ξ) y =
      finiteDirichletMultiplier support σ χ ξ * depthWave ξ y := by
  calc
    depthTranslationKernel support σ χ (depthWave ξ) y
        = support.sum fun m =>
            (χ m / (((m : ℕ) : ℂ) ^ (σ + 1)) * depthWave ξ (depthShift m)) * depthWave ξ y := by
              refine Finset.sum_congr rfl ?_
              intro m hm
              rw [show y + depthShift m = depthShift m + y by simp [add_comm]]
              rw [depthWave_add]
              ring
    _ = (support.sum fun m =>
            χ m / (((m : ℕ) : ℂ) ^ (σ + 1)) * depthWave ξ (depthShift m)) * depthWave ξ y := by
          rw [Finset.sum_mul]
    _ = finiteDirichletMultiplier support σ χ ξ * depthWave ξ y := by
          rw [finiteDirichletMultiplier_formula]

lemma spectralBlockingIff_on_wave (support : Finset ℕ+) (σ : ℕ) (χ : ℕ+ → ℂ) (ξ : ℝ) :
    finiteDirichletMultiplier support σ χ ξ = 0 ↔
      ∀ y, depthTranslationKernel support σ χ (depthWave ξ) y = 0 := by
  constructor
  · intro hmult y
    rw [depthTranslationKernel_on_wave, hmult, zero_mul]
  · intro hker
    have hw0 : depthWave ξ 0 = 1 := by
      simp [depthWave]
    specialize hker 0
    rw [depthTranslationKernel_on_wave, hw0, mul_one] at hker
    exact hker

/-- Paper-facing finite-support phase-depth spectrum theorem: logarithmic translates diagonalize on
depth-line plane waves, the diagonal factor is the corresponding finite Dirichlet series, and
spectral blocking is equivalent to vanishing of that multiplier.
    thm:phase-depth-spectrum-L -/
theorem paper_phase_depth_spectrum_l
    (support : Finset ℕ+) (σ : ℕ) (χ : ℕ+ → ℂ) :
    fourierDiagonalization support σ χ ∧
      dirichletMultiplierFormula support σ χ ∧
      spectralBlockingIff support σ χ := by
  refine ⟨?_, ?_⟩
  · intro ξ y
    exact depthTranslationKernel_on_wave support σ χ ξ y
  · refine ⟨?_, ?_⟩
    · intro ξ
      exact finiteDirichletMultiplier_formula support σ χ ξ
    · intro ξ
      exact spectralBlockingIff_on_wave support σ χ ξ

end

end Omega.UnitCirclePhaseArithmetic
