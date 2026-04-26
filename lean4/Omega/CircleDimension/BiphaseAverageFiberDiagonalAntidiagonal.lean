import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

namespace Omega.CircleDimension

noncomputable section

/-- The biphase average gate in midpoint/difference coordinates. -/
def cdim_biphase_average_fiber_diagonal_antidiagonal_gate (u v : ℝ) : ℂ :=
  Complex.exp ((((u + v) / 2 : ℝ) : ℂ) * Complex.I) * (Real.cos ((u - v) / 2) : ℂ)

/-- Paper-facing formulation of the midpoint/difference identities: swapping the two phases keeps
the same value, the diagonal gives the boundary branch, and the antidiagonal gives the zero
fiber. -/
def cdim_biphase_average_fiber_diagonal_antidiagonal_statement : Prop :=
  (∀ θ α : ℝ,
      cdim_biphase_average_fiber_diagonal_antidiagonal_gate (θ + α) (θ - α) =
        Complex.exp ((θ : ℂ) * Complex.I) * (Real.cos α : ℂ)) ∧
    (∀ θ α : ℝ,
      cdim_biphase_average_fiber_diagonal_antidiagonal_gate (θ - α) (θ + α) =
        Complex.exp ((θ : ℂ) * Complex.I) * (Real.cos α : ℂ)) ∧
    (∀ θ : ℝ,
      cdim_biphase_average_fiber_diagonal_antidiagonal_gate θ θ =
        Complex.exp ((θ : ℂ) * Complex.I)) ∧
    (∀ θ : ℝ,
      cdim_biphase_average_fiber_diagonal_antidiagonal_gate
          (θ + Real.pi / 2) (θ - Real.pi / 2) = 0) ∧
    (∀ θ : ℝ,
      cdim_biphase_average_fiber_diagonal_antidiagonal_gate
          (θ - Real.pi / 2) (θ + Real.pi / 2) = 0)

/-- Paper label: `thm:cdim-biphase-average-fiber-diagonal-antidiagonal`. -/
theorem paper_cdim_biphase_average_fiber_diagonal_antidiagonal :
    cdim_biphase_average_fiber_diagonal_antidiagonal_statement := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro θ α
    have hmid : (((θ + α) + (θ - α)) / 2 : ℝ) = θ := by ring
    have hdiff : (((θ + α) - (θ - α)) / 2 : ℝ) = α := by ring
    simp [cdim_biphase_average_fiber_diagonal_antidiagonal_gate, hmid, hdiff]
  · intro θ α
    have hmid : (((θ - α) + (θ + α)) / 2 : ℝ) = θ := by ring
    have hdiff : (((θ - α) - (θ + α)) / 2 : ℝ) = -α := by ring
    simp [cdim_biphase_average_fiber_diagonal_antidiagonal_gate, hmid, hdiff]
  · intro θ
    have hmid : (((θ + θ) / 2 : ℝ)) = θ := by ring
    have hdiff : (((θ - θ) / 2 : ℝ)) = 0 := by ring
    simp [cdim_biphase_average_fiber_diagonal_antidiagonal_gate, hmid, hdiff]
  · intro θ
    have hmid : (((θ + Real.pi / 2) + (θ - Real.pi / 2)) / 2 : ℝ) = θ := by ring
    have hdiff : (((θ + Real.pi / 2) - (θ - Real.pi / 2)) / 2 : ℝ) = Real.pi / 2 := by ring
    simp [cdim_biphase_average_fiber_diagonal_antidiagonal_gate, hmid, hdiff]
  · intro θ
    have hmid : (((θ - Real.pi / 2) + (θ + Real.pi / 2)) / 2 : ℝ) = θ := by ring
    have hdiff : (((θ - Real.pi / 2) - (θ + Real.pi / 2)) / 2 : ℝ) = -(Real.pi / 2) := by ring
    simp [cdim_biphase_average_fiber_diagonal_antidiagonal_gate, hmid, hdiff]

end

end Omega.CircleDimension
