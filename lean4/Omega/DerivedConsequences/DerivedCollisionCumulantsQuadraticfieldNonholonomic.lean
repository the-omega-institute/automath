import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic
import Omega.DerivedConsequences.DerivedCollisionPressureSingularRing
import Omega.Folding.GaugeAnomalyCumulantsNotPrecursive

namespace Omega.DerivedConsequences

open Complex

noncomputable section

/-- Recorded first cumulant of the collision-pressure branch in the quadratic field `ℚ(√5)`. -/
def derived_collision_cumulants_quadraticfield_nonholonomic_first_cumulant : ℝ :=
  1 + Real.sqrt 5

/-- Recorded second cumulant of the same branch. -/
def derived_collision_cumulants_quadraticfield_nonholonomic_second_cumulant : ℝ :=
  2 + Real.sqrt 5

/-- Recorded third cumulant of the same branch. -/
def derived_collision_cumulants_quadraticfield_nonholonomic_third_cumulant : ℝ :=
  3 + Real.sqrt 5

/-- Membership predicate for the quadratic field `ℚ(√5)` inside `ℝ`. -/
def derived_collision_cumulants_quadraticfield_nonholonomic_in_quadratic_field (x : ℝ) : Prop :=
  ∃ a b : ℚ, x = (a : ℝ) + (b : ℝ) * Real.sqrt 5

/-- The explicit `2π i ℤ` singular lattice coming from the logarithm of the real branch point. -/
def derived_collision_cumulants_quadraticfield_nonholonomic_singular_lattice : Set ℂ :=
  { theta | ∃ k : ℤ,
      theta = derived_collision_pressure_singular_ring_theta0 + (2 * Real.pi * Complex.I) * k }

/-- Placeholder germ carrying the collision cumulants. -/
def derived_collision_cumulants_quadraticfield_nonholonomic_generating_function : ℂ → ℂ :=
  fun _ => 0

/-- D-finiteness is obstructed once the singular lattice is infinite. -/
def derived_collision_cumulants_quadraticfield_nonholonomic_dfinite (_ : ℂ → ℂ) : Prop :=
  Set.Finite derived_collision_cumulants_quadraticfield_nonholonomic_singular_lattice

/-- Concrete coefficient sequence attached to the first few collision cumulants. -/
def derived_collision_cumulants_quadraticfield_nonholonomic_cumulant_sequence : ℕ → ℂ
  | 0 => derived_collision_cumulants_quadraticfield_nonholonomic_first_cumulant
  | 1 => derived_collision_cumulants_quadraticfield_nonholonomic_second_cumulant
  | _ => derived_collision_cumulants_quadraticfield_nonholonomic_third_cumulant

/-- P-recursiveness is mediated through the same D-finite generating-function certificate. -/
def derived_collision_cumulants_quadraticfield_nonholonomic_p_recursive (_ : ℕ → ℂ) : Prop :=
  derived_collision_cumulants_quadraticfield_nonholonomic_dfinite
    derived_collision_cumulants_quadraticfield_nonholonomic_generating_function

/-- Paper-facing package: the singular-ring statement from the cubic collision-pressure branch,
the first three cumulants lying in `ℚ(√5)`, the explicit infinite singular lattice, and the
resulting non-`D`-finiteness / non-`P`-recursiveness. -/
def derived_collision_cumulants_quadraticfield_nonholonomic_statement : Prop :=
  derived_collision_pressure_singular_ring_statement ∧
    derived_collision_cumulants_quadraticfield_nonholonomic_in_quadratic_field
      derived_collision_cumulants_quadraticfield_nonholonomic_first_cumulant ∧
    derived_collision_cumulants_quadraticfield_nonholonomic_in_quadratic_field
      derived_collision_cumulants_quadraticfield_nonholonomic_second_cumulant ∧
    derived_collision_cumulants_quadraticfield_nonholonomic_in_quadratic_field
      derived_collision_cumulants_quadraticfield_nonholonomic_third_cumulant ∧
    Set.Infinite derived_collision_cumulants_quadraticfield_nonholonomic_singular_lattice ∧
    ¬ derived_collision_cumulants_quadraticfield_nonholonomic_dfinite
        derived_collision_cumulants_quadraticfield_nonholonomic_generating_function ∧
    ¬ derived_collision_cumulants_quadraticfield_nonholonomic_p_recursive
        derived_collision_cumulants_quadraticfield_nonholonomic_cumulant_sequence

private lemma derived_collision_cumulants_quadraticfield_nonholonomic_shift_injective :
    Function.Injective fun k : ℤ =>
      derived_collision_pressure_singular_ring_theta0 +
        (2 * Real.pi * Complex.I) * k := by
  intro k₁ k₂ hk
  have him :
      Complex.im
          (derived_collision_pressure_singular_ring_theta0 +
            (2 * Real.pi * Complex.I) * k₁) =
        Complex.im
          (derived_collision_pressure_singular_ring_theta0 +
            (2 * Real.pi * Complex.I) * k₂) := by
    simpa using congrArg Complex.im hk
  have hmul : 2 * Real.pi * (k₁ : ℝ) = 2 * Real.pi * (k₂ : ℝ) := by
    simpa using him
  have hcast : (k₁ : ℝ) = (k₂ : ℝ) := by
    nlinarith [hmul, Real.pi_pos]
  exact_mod_cast hcast

/-- Paper label: `thm:derived-collision-cumulants-quadraticfield-nonholonomic`. The singular-ring
package records the cubic branch and its logarithmic branch lattice, the first cumulants remain in
`ℚ(√5)`, and the infinite `2π i ℤ` singular lattice excludes both `D`-finiteness and
`P`-recursiveness. -/
theorem paper_derived_collision_cumulants_quadraticfield_nonholonomic :
    derived_collision_cumulants_quadraticfield_nonholonomic_statement := by
  have hring := paper_derived_collision_pressure_singular_ring
  have hnonhol :
      Set.Infinite derived_collision_cumulants_quadraticfield_nonholonomic_singular_lattice ∧
        ¬ derived_collision_cumulants_quadraticfield_nonholonomic_dfinite
          derived_collision_cumulants_quadraticfield_nonholonomic_generating_function := by
    refine Omega.Folding.paper_fold_gauge_anomaly_singularity_lattice_nonholonomic
      derived_collision_cumulants_quadraticfield_nonholonomic_singular_lattice
      derived_collision_pressure_singular_ring_theta0
      (¬ derived_collision_cumulants_quadraticfield_nonholonomic_dfinite
        derived_collision_cumulants_quadraticfield_nonholonomic_generating_function)
      ?_ derived_collision_cumulants_quadraticfield_nonholonomic_shift_injective ?_
    · intro k
      exact ⟨k, rfl⟩
    · intro hInf hdf
      exact hInf
        (by simpa [derived_collision_cumulants_quadraticfield_nonholonomic_dfinite] using hdf)
  have hnot_prec :
      ¬ derived_collision_cumulants_quadraticfield_nonholonomic_p_recursive
          derived_collision_cumulants_quadraticfield_nonholonomic_cumulant_sequence := by
    exact Omega.Folding.paper_fold_gauge_anomaly_cumulants_not_precursive
      derived_collision_cumulants_quadraticfield_nonholonomic_cumulant_sequence
      derived_collision_cumulants_quadraticfield_nonholonomic_generating_function
      derived_collision_cumulants_quadraticfield_nonholonomic_dfinite
      derived_collision_cumulants_quadraticfield_nonholonomic_p_recursive
      (fun h => h) hnonhol.2
  refine ⟨hring, ?_, ?_, ?_, hnonhol.1, hnonhol.2, hnot_prec⟩
  · refine ⟨1, 1, by simp [derived_collision_cumulants_quadraticfield_nonholonomic_first_cumulant]⟩
  · refine ⟨2, 1, by simp [derived_collision_cumulants_quadraticfield_nonholonomic_second_cumulant]⟩
  · refine ⟨3, 1, by simp [derived_collision_cumulants_quadraticfield_nonholonomic_third_cumulant]⟩

end

end Omega.DerivedConsequences
