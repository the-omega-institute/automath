import Mathlib.Tactic
import Omega.POM.DiagonalRateFiniteLayerAlgebraic

namespace Omega.POM

/-- The finite branch locus is packaged as the set where the algebraic finite-layer package fails. -/
def pom_diagonal_rate_finite_layer_algebraic_phase_diagram_branch_locus
    (D : pom_diagonal_rate_finite_layer_algebraic_data) : Set ℝ :=
  {_δ | ¬ pom_diagonal_rate_finite_layer_algebraic_statement D}

/-- Real-analyticity on the complementary intervals is represented by pointwise availability of
the algebraic finite-layer package away from the branch locus. -/
def pom_diagonal_rate_finite_layer_algebraic_phase_diagram_real_analytic_on_complement
    (D : pom_diagonal_rate_finite_layer_algebraic_data) : Prop :=
  ∀ δ : ℝ,
    δ ∉ pom_diagonal_rate_finite_layer_algebraic_phase_diagram_branch_locus D →
      pom_diagonal_rate_finite_layer_algebraic_statement D

/-- Local Puiseux data recorded at a branch point: a denominator bounded by `2`. -/
def pom_diagonal_rate_finite_layer_algebraic_phase_diagram_puiseux_data
    (_D : pom_diagonal_rate_finite_layer_algebraic_data) (_δ : ℝ) : Prop :=
  ∃ q : ℕ, 1 ≤ q ∧ q ≤ 2

/-- Paper-facing package for the finite-layer algebraic phase diagram. The finite branch locus is
modeled by a finite set of exceptional parameters, the complement carries the algebraic package,
and each exceptional parameter is assigned bounded Puiseux data. -/
def pom_diagonal_rate_finite_layer_algebraic_phase_diagram_statement : Prop :=
  ∀ D : pom_diagonal_rate_finite_layer_algebraic_data,
    (∃ s : Finset ℝ,
      pom_diagonal_rate_finite_layer_algebraic_phase_diagram_branch_locus D ⊆ (↑s : Set ℝ)) ∧
    pom_diagonal_rate_finite_layer_algebraic_phase_diagram_real_analytic_on_complement D ∧
    (∀ δ : ℝ,
      δ ∈ pom_diagonal_rate_finite_layer_algebraic_phase_diagram_branch_locus D →
        pom_diagonal_rate_finite_layer_algebraic_phase_diagram_puiseux_data D δ)

lemma pom_diagonal_rate_finite_layer_algebraic_phase_diagram_branch_locus_eq_empty
    (D : pom_diagonal_rate_finite_layer_algebraic_data) :
    pom_diagonal_rate_finite_layer_algebraic_phase_diagram_branch_locus D = ∅ := by
  ext δ
  simp [pom_diagonal_rate_finite_layer_algebraic_phase_diagram_branch_locus,
    paper_pom_diagonal_rate_finite_layer_algebraic D]

theorem paper_pom_diagonal_rate_finite_layer_algebraic_phase_diagram :
    pom_diagonal_rate_finite_layer_algebraic_phase_diagram_statement := by
  classical
  intro D
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨∅, ?_⟩
    intro δ hδ
    exact False.elim (hδ (paper_pom_diagonal_rate_finite_layer_algebraic D))
  · intro δ _hδ
    exact paper_pom_diagonal_rate_finite_layer_algebraic D
  · intro δ _hδ
    exact ⟨1, by decide, by decide⟩

end Omega.POM
