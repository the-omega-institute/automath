import Omega.Folding.GraphCycleLatticeThetaModularInversion
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

namespace Omega.Folding

/-- The dual-character phase contributed by translating the theta sum by an affine lattice class. -/
noncomputable def graphCycleAffinePhase (ξ ψ₀ : ℤ) : ℂ :=
  Complex.exp (((ξ * ψ₀ : ℤ) : ℂ) * (2 * Real.pi * Complex.I))

/-- Scalar affine-theta model: the translated kernel is the base Poisson kernel times its dual
phase factor. -/
noncomputable def graphCycleAffineThetaKernel
    (rank : ℕ) (gammaDet dualMass t : ℚ) (ξ ψ₀ : ℤ) : ℂ :=
  (graphCycleThetaKernel rank gammaDet dualMass t : ℂ) * graphCycleAffinePhase ξ ψ₀

/-- Paper label: `cor:graph-cycle-affine-torsor-theta-poisson-phase`.

In the scalar cycle-lattice model, translating by an affine torsor class only inserts the expected
dual-character phase, and that phase is unchanged by integral lattice shifts. -/
theorem paper_graph_cycle_affine_torsor_theta_poisson_phase
    (rank : ℕ) (gammaDet dualMass t : ℚ) (ξ ψ₀ k : ℤ) (hγ : gammaDet ≠ 0) (ht : t ≠ 0) :
    graphCycleAffineThetaKernel rank gammaDet dualMass t ξ ψ₀ =
      (((1 / t ^ (2 * rank) : ℚ) : ℂ) *
        graphCycleAffineThetaKernel rank gammaDet dualMass (1 / t) ξ ψ₀) ∧
      graphCycleAffinePhase ξ (ψ₀ + k) = graphCycleAffinePhase ξ ψ₀ ∧
      graphCycleAffineThetaKernel rank gammaDet dualMass t ξ (ψ₀ + k) =
        graphCycleAffineThetaKernel rank gammaDet dualMass t ξ ψ₀ := by
  rcases paper_graph_cycle_lattice_theta_modular_inversion rank gammaDet dualMass t hγ ht with
    ⟨hmod, -, -⟩
  have hmodC :
      ((graphCycleThetaKernel rank gammaDet dualMass t : ℚ) : ℂ) =
        (((1 / t ^ (2 * rank)) * graphCycleThetaKernel rank gammaDet dualMass (1 / t) : ℚ) : ℂ) :=
    congrArg (fun q : ℚ => (q : ℂ)) hmod
  have hphase_period : graphCycleAffinePhase ξ (ψ₀ + k) = graphCycleAffinePhase ξ ψ₀ := by
    unfold graphCycleAffinePhase
    rw [show ((((ξ * (ψ₀ + k) : ℤ) : ℂ) * (2 * Real.pi * Complex.I))) =
        (((ξ * ψ₀ : ℤ) : ℂ) * (2 * Real.pi * Complex.I)) +
          (((ξ * k : ℤ) : ℂ) * (2 * Real.pi * Complex.I)) by
        push_cast
        ring]
    have hperiod :
        Complex.exp ((((ξ * k : ℤ) : ℂ) * (2 * Real.pi * Complex.I))) = 1 := by
      simpa using Complex.exp_int_mul_two_pi_mul_I (ξ * k)
    rw [Complex.exp_add, hperiod]
    simp
  refine ⟨?_, hphase_period, ?_⟩
  · unfold graphCycleAffineThetaKernel
    rw [hmodC]
    simp [mul_left_comm, mul_comm]
  · unfold graphCycleAffineThetaKernel
    rw [hphase_period]

end Omega.Folding
