import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic
import Omega.POM.FiberRewriteIndependentSum
import Omega.POM.PathIndsetThermoConstants

open scoped BigOperators

namespace Omega.POM

noncomputable section

/-- Unit activities on every path component in the fiber rewrite. -/
def pom_fiber_rewrite_mean_var_density_unit_activity (lengths : List ℕ)
    (i : Fin lengths.length) (_j : Fin (lengths.get i)) : ℝ :=
  1

/-- The total path length, expressed on the same finite index set used by `List.get`. -/
def pom_fiber_rewrite_mean_var_density_total_length (lengths : List ℕ) : ℝ :=
  ∑ i : Fin lengths.length, (lengths.get i : ℝ)

/-- Package for the unit-activity mean/variance density rewrite over a list of path lengths. -/
def pom_fiber_rewrite_mean_var_density_statement (lengths : List ℕ) : Prop :=
  let alpha := pom_fiber_rewrite_mean_var_density_unit_activity lengths
  Nonempty (((i : Fin lengths.length) → Omega.X (lengths.get i)) ≃
    ((i : Fin lengths.length) → Omega.PathIndSets (lengths.get i))) ∧
    ∃ p : (i : Fin lengths.length) → Fin (lengths.get i) → ℝ,
      (∀ i j, 0 < p i j ∧ p i j < 1) ∧
      (∀ t : ℝ,
        (∏ i : Fin lengths.length,
            ∏ j : Fin (lengths.get i), ((alpha i j + t) / (alpha i j + 1))) =
          ∏ i : Fin lengths.length,
            ∏ j : Fin (lengths.get i), (1 - p i j + p i j * t)) ∧
      (∑ i : Fin lengths.length, ∑ j : Fin (lengths.get i), p i j =
        pom_fiber_rewrite_mean_var_density_total_length lengths / 2) ∧
      (∑ i : Fin lengths.length, ∑ j : Fin (lengths.get i), p i j * (1 - p i j) =
        pom_fiber_rewrite_mean_var_density_total_length lengths / 4) ∧
      pom_path_indset_thermo_constants_statement

private lemma pom_fiber_rewrite_mean_var_density_mean_sum (lengths : List ℕ) :
    (∑ i : Fin lengths.length,
        ∑ j : Fin (lengths.get i),
          (1 / (1 + pom_fiber_rewrite_mean_var_density_unit_activity lengths i j) : ℝ)) =
      pom_fiber_rewrite_mean_var_density_total_length lengths / 2 := by
  rw [pom_fiber_rewrite_mean_var_density_total_length, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _hi
  simp [pom_fiber_rewrite_mean_var_density_unit_activity]
  norm_num

private lemma pom_fiber_rewrite_mean_var_density_variance_sum (lengths : List ℕ) :
    (∑ i : Fin lengths.length,
        ∑ j : Fin (lengths.get i),
          (pom_fiber_rewrite_mean_var_density_unit_activity lengths i j /
            (1 + pom_fiber_rewrite_mean_var_density_unit_activity lengths i j) ^ 2 : ℝ)) =
      pom_fiber_rewrite_mean_var_density_total_length lengths / 4 := by
  rw [pom_fiber_rewrite_mean_var_density_total_length, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _hi
  simp [pom_fiber_rewrite_mean_var_density_unit_activity]
  norm_num

/-- Paper label: `cor:pom-fiber-rewrite-mean-var-density`. -/
theorem paper_pom_fiber_rewrite_mean_var_density (lengths : List ℕ) :
    pom_fiber_rewrite_mean_var_density_statement lengths := by
  let alpha := pom_fiber_rewrite_mean_var_density_unit_activity lengths
  have halpha : ∀ i j, 0 < alpha i j := by
    intro i j
    simp [alpha, pom_fiber_rewrite_mean_var_density_unit_activity]
  rcases paper_pom_fiber_rewrite_independent_sum lengths alpha halpha with
    ⟨hequiv, p, hp, hgen, hmean, hvar⟩
  refine ⟨hequiv, p, hp, hgen, ?_, ?_, paper_pom_path_indset_thermo_constants⟩
  · calc
      (∑ i : Fin lengths.length, ∑ j : Fin (lengths.get i), p i j)
          = ∑ i : Fin lengths.length, ∑ j : Fin (lengths.get i), (1 / (1 + alpha i j)) :=
            hmean
      _ = pom_fiber_rewrite_mean_var_density_total_length lengths / 2 := by
        simpa [alpha] using pom_fiber_rewrite_mean_var_density_mean_sum lengths
  · calc
      (∑ i : Fin lengths.length, ∑ j : Fin (lengths.get i), p i j * (1 - p i j))
          = ∑ i : Fin lengths.length,
              ∑ j : Fin (lengths.get i), (alpha i j / (1 + alpha i j) ^ 2) := hvar
      _ = pom_fiber_rewrite_mean_var_density_total_length lengths / 4 := by
        simpa [alpha] using pom_fiber_rewrite_mean_var_density_variance_sum lengths

end

end Omega.POM
