import Mathlib.Tactic
import Omega.POM.MaxentMarkovSpectrumSingleShotInversion

open scoped BigOperators

namespace Omega.POM

/-- Concrete rate/spectrum audit datum for the one-state maxent Markov package. -/
structure pom_maxent_markov_spectrum_rate_complete_invariant_data where
  pom_maxent_markov_spectrum_rate_complete_invariant_kappa : ℝ
  pom_maxent_markov_spectrum_rate_complete_invariant_kappa_pos :
    0 < pom_maxent_markov_spectrum_rate_complete_invariant_kappa

/-- The rate slope is the reciprocal dual parameter recorded by the one-state model. -/
noncomputable def pom_maxent_markov_spectrum_rate_complete_invariant_rate_slope
    (D : pom_maxent_markov_spectrum_rate_complete_invariant_data) : ℝ :=
  1 / D.pom_maxent_markov_spectrum_rate_complete_invariant_kappa

/-- The audited one-state distribution. Up to relabeling, every recovered model is this one. -/
def pom_maxent_markov_spectrum_rate_complete_invariant_distribution : Fin 1 → ℝ :=
  fun _ => 1

/-- Concrete statement: the reciprocal rate slope recovers `κ`, and the single-shot spectrum
identifies the unique one-point distribution. -/
def pom_maxent_markov_spectrum_rate_complete_invariant_statement
    (D : pom_maxent_markov_spectrum_rate_complete_invariant_data) : Prop :=
  let κ := D.pom_maxent_markov_spectrum_rate_complete_invariant_kappa
  let slope := pom_maxent_markov_spectrum_rate_complete_invariant_rate_slope D
  let t : Fin 1 → ℝ := fun _ => κ + 1
  let P : ℝ → ℝ := fun z => κ + 1 - z
  let Q : ℝ → ℝ := fun z => z * (-1) + κ * P z
  let w := pom_maxent_markov_spectrum_rate_complete_invariant_distribution
  slope = 1 / κ ∧
    (∀ κ' : ℝ, 0 < κ' → 1 / κ' = slope → κ' = κ) ∧
    (∀ z : ℝ, Q z = 0 ↔ z = 1 / slope) ∧
    (∀ x : Fin 1, P (t x) = 0) ∧
    (∑ x : Fin 1, w x = 1)

/-- Paper label: `cor:pom-maxent-markov-spectrum-rate-complete-invariant`. -/
theorem paper_pom_maxent_markov_spectrum_rate_complete_invariant
    (D : pom_maxent_markov_spectrum_rate_complete_invariant_data) :
    pom_maxent_markov_spectrum_rate_complete_invariant_statement D := by
  let κ := D.pom_maxent_markov_spectrum_rate_complete_invariant_kappa
  have hsingle :=
    paper_pom_maxent_markov_spectrum_single_shot_inversion κ
      D.pom_maxent_markov_spectrum_rate_complete_invariant_kappa_pos
  dsimp [pom_maxent_markov_spectrum_rate_complete_invariant_statement] at hsingle ⊢
  rcases hsingle with ⟨_, hroot, hP, hw⟩
  refine ⟨rfl, ?_, ?_, hP, hw⟩
  · intro κ' hκ' hslope
    have hκ_ne : κ ≠ 0 := ne_of_gt D.pom_maxent_markov_spectrum_rate_complete_invariant_kappa_pos
    have hκ'_ne : κ' ≠ 0 := ne_of_gt hκ'
    have hrecip : 1 / κ' = 1 / κ := by
      simpa [pom_maxent_markov_spectrum_rate_complete_invariant_rate_slope] using hslope
    field_simp [hκ_ne, hκ'_ne] at hrecip
    linarith
  · intro z
    have hκ_ne : κ ≠ 0 := ne_of_gt D.pom_maxent_markov_spectrum_rate_complete_invariant_kappa_pos
    have hslope_inv :
        1 / pom_maxent_markov_spectrum_rate_complete_invariant_rate_slope D = κ := by
      change 1 / (1 / κ) = κ
      field_simp [hκ_ne]
    simpa [hslope_inv] using hroot z

end Omega.POM
