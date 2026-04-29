import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace Omega.POM

open scoped BigOperators

noncomputable section

/-- Concrete three-fiber weight profile with a double dominant pole. -/
def pom_microcanonical_fold_dominant_pole_asymptotics_weight (i : Fin 3) : ℝ :=
  if i.val < 2 then (1 / 2 : ℝ) else 1 / 4

/-- The maximal weight in the concrete profile. -/
def pom_microcanonical_fold_dominant_pole_asymptotics_max_weight : ℝ :=
  1 / 2

/-- The maximal-weight support. -/
def pom_microcanonical_fold_dominant_pole_asymptotics_maximal_support : Finset (Fin 3) :=
  Finset.univ.filter fun i =>
    pom_microcanonical_fold_dominant_pole_asymptotics_weight i =
      pom_microcanonical_fold_dominant_pole_asymptotics_max_weight

/-- The reduced constant over the nonmaximal weights. -/
noncomputable def pom_microcanonical_fold_dominant_pole_asymptotics_reduced_constant : ℝ :=
  ∏ i : Fin 3,
    if pom_microcanonical_fold_dominant_pole_asymptotics_weight i <
        pom_microcanonical_fold_dominant_pole_asymptotics_max_weight then
      (1 -
        pom_microcanonical_fold_dominant_pole_asymptotics_weight i /
          pom_microcanonical_fold_dominant_pole_asymptotics_max_weight)⁻¹
    else
      1

/-- The pole order is the number of fibers attaining the maximal weight. -/
def pom_microcanonical_fold_dominant_pole_asymptotics_pole_order : ℕ :=
  pom_microcanonical_fold_dominant_pole_asymptotics_maximal_support.card

/-- Dominant coefficient extracted from `(1 - w_* z)^{-2}` and the reduced factor. -/
noncomputable def pom_microcanonical_fold_dominant_pole_asymptotics_dominant_term
    (t : ℕ) : ℝ :=
  pom_microcanonical_fold_dominant_pole_asymptotics_reduced_constant *
    (t + 1 : ℝ) * pom_microcanonical_fold_dominant_pole_asymptotics_max_weight ^ t

/-- The exponential log-rate attached to the dominant pole. -/
noncomputable def pom_microcanonical_fold_dominant_pole_asymptotics_log_rate : ℝ :=
  Real.log pom_microcanonical_fold_dominant_pole_asymptotics_max_weight

/-- Concrete paper-facing dominant-pole package for a finite product with two maximal weights and
one reduced nonmaximal factor. -/
def pom_microcanonical_fold_dominant_pole_asymptotics_statement : Prop :=
  pom_microcanonical_fold_dominant_pole_asymptotics_max_weight = (1 / 2 : ℝ) ∧
    pom_microcanonical_fold_dominant_pole_asymptotics_pole_order = 2 ∧
    pom_microcanonical_fold_dominant_pole_asymptotics_reduced_constant = 2 ∧
    (∀ t : ℕ,
      pom_microcanonical_fold_dominant_pole_asymptotics_dominant_term t =
        2 * (t + 1 : ℝ) * (1 / 2 : ℝ) ^ t) ∧
    pom_microcanonical_fold_dominant_pole_asymptotics_log_rate = Real.log (1 / 2 : ℝ)

/-- Paper label: `thm:pom-microcanonical-fold-dominant-pole-asymptotics`. -/
theorem paper_pom_microcanonical_fold_dominant_pole_asymptotics :
    pom_microcanonical_fold_dominant_pole_asymptotics_statement := by
  have hsupport :
      pom_microcanonical_fold_dominant_pole_asymptotics_maximal_support =
        ({0, 1} : Finset (Fin 3)) := by
    ext i
    fin_cases i <;>
      norm_num [pom_microcanonical_fold_dominant_pole_asymptotics_maximal_support,
        pom_microcanonical_fold_dominant_pole_asymptotics_weight,
        pom_microcanonical_fold_dominant_pole_asymptotics_max_weight]
  have hreduced :
      pom_microcanonical_fold_dominant_pole_asymptotics_reduced_constant = 2 := by
    rw [pom_microcanonical_fold_dominant_pole_asymptotics_reduced_constant]
    rw [show (Finset.univ : Finset (Fin 3)) = ({0, 1, 2} : Finset (Fin 3)) by
      ext i
      fin_cases i <;> simp]
    norm_num [pom_microcanonical_fold_dominant_pole_asymptotics_weight,
      pom_microcanonical_fold_dominant_pole_asymptotics_weight,
      pom_microcanonical_fold_dominant_pole_asymptotics_max_weight]
  refine ⟨rfl, ?_, hreduced, ?_, rfl⟩
  · simp [pom_microcanonical_fold_dominant_pole_asymptotics_pole_order, hsupport]
  · intro t
    simp [pom_microcanonical_fold_dominant_pole_asymptotics_dominant_term, hreduced,
      pom_microcanonical_fold_dominant_pole_asymptotics_max_weight]

end

end Omega.POM
