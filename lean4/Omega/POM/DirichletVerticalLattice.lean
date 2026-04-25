import Mathlib.Tactic

namespace Omega.POM

noncomputable section

/-- Concrete logarithmic-coordinate data for the Dirichlet vertical lattice. The denominator
`lambdaLog` is the logarithmic scale, `radiusLog` fixes the real coordinate, and `argR0` fixes the
base argument branch. -/
structure pom_dirichlet_vertical_lattice_data where
  lambdaLog : ℝ
  radiusLog : ℝ
  argR0 : ℝ
  lambdaLog_ne_zero : lambdaLog ≠ 0

namespace pom_dirichlet_vertical_lattice_data

/-- Real coordinate of the logarithmic solution branch. -/
def realCoordinate (D : pom_dirichlet_vertical_lattice_data) (_k : ℤ) : ℝ :=
  D.radiusLog / D.lambdaLog

/-- Imaginary coordinate of the logarithmic solution branch. -/
def imaginaryCoordinate (D : pom_dirichlet_vertical_lattice_data) (k : ℤ) : ℝ :=
  (D.argR0 + 2 * Real.pi * (k : ℝ)) / D.lambdaLog

/-- Every integer branch lies on the same vertical line and solves the argument equation. -/
def solution_set_is_vertical_lattice (D : pom_dirichlet_vertical_lattice_data) : Prop :=
  (∀ k : ℤ, D.realCoordinate k = D.radiusLog / D.lambdaLog) ∧
    ∀ k : ℤ, D.lambdaLog * D.imaginaryCoordinate k =
      D.argR0 + 2 * Real.pi * (k : ℝ)

/-- Consecutive logarithmic branches have constant imaginary spacing. -/
def constant_imaginary_spacing (D : pom_dirichlet_vertical_lattice_data) : Prop :=
  ∀ k : ℤ, D.imaginaryCoordinate (k + 1) - D.imaginaryCoordinate k =
    2 * Real.pi / D.lambdaLog

/-- If the chosen argument branch is `π`, as for a negative real pole, the vertical lattice has
the half-odd-integer argument form. -/
def negative_real_specialization (D : pom_dirichlet_vertical_lattice_data) : Prop :=
  D.argR0 = Real.pi →
    ∀ k : ℤ, D.imaginaryCoordinate k =
      ((2 * (k : ℝ) + 1) * Real.pi) / D.lambdaLog

end pom_dirichlet_vertical_lattice_data

open pom_dirichlet_vertical_lattice_data

/-- Paper label: `lem:pom-dirichlet-vertical-lattice`. Solving the logarithmic branch equation
gives a fixed real coordinate and a vertical arithmetic lattice in the imaginary coordinate; for a
negative real pole the argument branch is the usual half-odd-integer lattice. -/
theorem paper_pom_dirichlet_vertical_lattice (D : pom_dirichlet_vertical_lattice_data) :
    D.solution_set_is_vertical_lattice ∧ D.constant_imaginary_spacing ∧
      D.negative_real_specialization := by
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · intro k
      rfl
    · intro k
      unfold imaginaryCoordinate
      field_simp [D.lambdaLog_ne_zero]
  · intro k
    unfold imaginaryCoordinate
    field_simp [D.lambdaLog_ne_zero]
    norm_num
    ring
  · intro harg k
    unfold imaginaryCoordinate
    rw [harg]
    field_simp [D.lambdaLog_ne_zero]
    ring

end

end Omega.POM
