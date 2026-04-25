import Mathlib.Tactic
import Omega.POM.DerivedSchurTopLayerCriterion

namespace Omega.DerivedConsequences

open Omega.POM
open Omega.POM.SchurPartitionIndex

/-- The unique dominant partition selected in the `S₂` singleton-dominant seed. -/
def derived_schur_unique_dominant_partition_selection_nu_star :
    Omega.POM.SchurPartitionIndex :=
  cycle

/-- Positive scalar relating the top coefficient to the dominant-cycle character. -/
def derived_schur_unique_dominant_partition_selection_positive_scalar : ℝ :=
  1

/-- The dominant-cycle character factor used in the singleton selection law. -/
def derived_schur_unique_dominant_partition_selection_character_factor : ℝ :=
  Omega.POM.schurCharacter
    derived_schur_unique_dominant_partition_selection_nu_star
    derived_schur_unique_dominant_partition_selection_nu_star

/-- Paper-facing singleton-dominant selection statement in the concrete `S₂` seed. -/
def derived_schur_unique_dominant_partition_selection_statement : Prop :=
  Omega.POM.derived_schur_top_layer_criterion_visible
      derived_schur_unique_dominant_partition_selection_nu_star ∧
    ¬ Omega.POM.derived_schur_top_layer_criterion_visible split ∧
    Omega.POM.derived_schur_top_layer_criterion_b_lambda
        derived_schur_unique_dominant_partition_selection_nu_star =
      derived_schur_unique_dominant_partition_selection_positive_scalar *
        derived_schur_unique_dominant_partition_selection_character_factor ∧
    0 < derived_schur_unique_dominant_partition_selection_positive_scalar ∧
    derived_schur_unique_dominant_partition_selection_character_factor ≠ 0

/-- Paper label: `cor:derived-schur-unique-dominant-partition-selection`. The top-layer
criterion rewrites visibility as nonvanishing of `b_λ`; in the singleton-dominant `S₂` seed the
selected dominant partition is the cycle class, whose coefficient is a positive scalar multiple of
the cycle character, while the other channel is cancelled. -/
theorem paper_derived_schur_unique_dominant_partition_selection :
    derived_schur_unique_dominant_partition_selection_statement := by
  rcases Omega.POM.paper_derived_schur_top_layer_criterion with ⟨_, hVisible, _⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (hVisible derived_schur_unique_dominant_partition_selection_nu_star).2 <| by
      simp [derived_schur_unique_dominant_partition_selection_nu_star,
        Omega.POM.derived_schur_top_layer_criterion_b_lambda]
  · intro hSplitVisible
    have hSplitCoeff :
        Omega.POM.derived_schur_top_layer_criterion_b_lambda split ≠ 0 :=
      (hVisible split).1 hSplitVisible
    simp [Omega.POM.derived_schur_top_layer_criterion_b_lambda] at hSplitCoeff
  · norm_num [derived_schur_unique_dominant_partition_selection_nu_star,
      derived_schur_unique_dominant_partition_selection_positive_scalar,
      derived_schur_unique_dominant_partition_selection_character_factor,
      Omega.POM.derived_schur_top_layer_criterion_b_lambda, Omega.POM.schurCharacter]
  · norm_num [derived_schur_unique_dominant_partition_selection_positive_scalar]
  · norm_num [derived_schur_unique_dominant_partition_selection_nu_star,
      derived_schur_unique_dominant_partition_selection_character_factor,
      Omega.POM.schurCharacter]

end Omega.DerivedConsequences
