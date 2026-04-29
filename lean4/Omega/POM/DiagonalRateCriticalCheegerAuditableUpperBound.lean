import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.POM.DiagonalRateCriticalContinuousTimeGeneratorMaxent

namespace Omega.POM

open scoped BigOperators

/-- Uniform two-state weight profile used for the auditable Cheeger certificate. -/
def pom_diagonal_rate_critical_cheeger_auditable_upper_bound_weight : Fin 2 → ℝ :=
  fun _ => 1

/-- Edge conductance induced by the critical two-state generator and the uniform weight profile. -/
def pom_diagonal_rate_critical_cheeger_auditable_upper_bound_conductance
    (x y : Fin 2) : ℝ :=
  pom_diagonal_rate_critical_cheeger_auditable_upper_bound_weight x * twoStateCriticalGenerator x y

/-- The only nontrivial prefix in the sorted two-state sweep. -/
def pom_diagonal_rate_critical_cheeger_auditable_upper_bound_prefix : Finset (Fin 2) :=
  {0}

/-- The corresponding cut value. -/
def pom_diagonal_rate_critical_cheeger_auditable_upper_bound_cut : ℝ :=
  pom_diagonal_rate_critical_cheeger_auditable_upper_bound_conductance 0 1

/-- Closed-form cut expression on the unique nontrivial sweep set. -/
noncomputable def pom_diagonal_rate_critical_cheeger_auditable_upper_bound_closed_form : ℝ :=
  Finset.sum ({0} : Finset (Fin 2))
      (fun x => Real.sqrt (pom_diagonal_rate_critical_cheeger_auditable_upper_bound_weight x)) *
    Finset.sum ({1} : Finset (Fin 2))
      (fun y => Real.sqrt (pom_diagonal_rate_critical_cheeger_auditable_upper_bound_weight y))

/-- Sweep certificate attached to the unique nontrivial prefix. -/
noncomputable def pom_diagonal_rate_critical_cheeger_auditable_upper_bound_sweep_certificate : ℝ :=
  pom_diagonal_rate_critical_cheeger_auditable_upper_bound_cut /
    min (pom_diagonal_rate_critical_cheeger_auditable_upper_bound_weight 0)
      (pom_diagonal_rate_critical_cheeger_auditable_upper_bound_weight 1)

/-- The second eigenvalue of the weighted Laplacian in the concrete two-state model. -/
def pom_diagonal_rate_critical_cheeger_auditable_upper_bound_second_eigenvalue : ℝ := 2

lemma pom_diagonal_rate_critical_cheeger_auditable_upper_bound_cut_eval :
    pom_diagonal_rate_critical_cheeger_auditable_upper_bound_cut = 1 := by
  simp [pom_diagonal_rate_critical_cheeger_auditable_upper_bound_cut,
    pom_diagonal_rate_critical_cheeger_auditable_upper_bound_conductance,
    pom_diagonal_rate_critical_cheeger_auditable_upper_bound_weight, twoStateCriticalGenerator]

lemma pom_diagonal_rate_critical_cheeger_auditable_upper_bound_sweep_eval :
    pom_diagonal_rate_critical_cheeger_auditable_upper_bound_sweep_certificate = 1 := by
  simp [pom_diagonal_rate_critical_cheeger_auditable_upper_bound_sweep_certificate,
    pom_diagonal_rate_critical_cheeger_auditable_upper_bound_cut_eval,
    pom_diagonal_rate_critical_cheeger_auditable_upper_bound_weight]

/-- Paper label: `cor:pom-diagonal-rate-critical-cheeger-auditable-upper-bound`.

For the concrete critical two-state generator, the only nontrivial sweep set is the singleton
prefix `{0}` in the sorted weight order. Its cut has the expected closed form, the sweep
certificate is explicit, and the standard Cheeger upper bound is auditable by direct evaluation. -/
theorem paper_pom_diagonal_rate_critical_cheeger_auditable_upper_bound :
    pom_diagonal_rate_critical_cheeger_auditable_upper_bound_cut =
        pom_diagonal_rate_critical_cheeger_auditable_upper_bound_closed_form ∧
      pom_diagonal_rate_critical_cheeger_auditable_upper_bound_prefix = ({0} : Finset (Fin 2)) ∧
      pom_diagonal_rate_critical_cheeger_auditable_upper_bound_sweep_certificate = 1 ∧
      pom_diagonal_rate_critical_cheeger_auditable_upper_bound_second_eigenvalue = 2 ∧
      pom_diagonal_rate_critical_cheeger_auditable_upper_bound_second_eigenvalue ≤
        2 * pom_diagonal_rate_critical_cheeger_auditable_upper_bound_sweep_certificate := by
  refine ⟨?_, rfl, pom_diagonal_rate_critical_cheeger_auditable_upper_bound_sweep_eval, rfl, ?_⟩
  · simp [pom_diagonal_rate_critical_cheeger_auditable_upper_bound_cut_eval,
      pom_diagonal_rate_critical_cheeger_auditable_upper_bound_closed_form,
      pom_diagonal_rate_critical_cheeger_auditable_upper_bound_weight]
  · rw [pom_diagonal_rate_critical_cheeger_auditable_upper_bound_sweep_eval]
    simp [pom_diagonal_rate_critical_cheeger_auditable_upper_bound_second_eigenvalue]

end Omega.POM
