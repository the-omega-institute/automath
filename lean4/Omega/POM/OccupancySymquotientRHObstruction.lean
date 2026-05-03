import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
import Omega.POM.ExcitationFilterLinearBound
import Omega.POM.FirstVariationFidelityRHBreaking

namespace Omega.POM

/-- The first obstruction conclusion: an occupancy-only symmetric quotient is first-variation
faithful at every large order, so the existing first-variation wrapper forces eventual RH
breaking. -/
def pom_occupancy_symquotient_rh_obstruction_eventual_breaking_statement : Prop :=
  ∀ (a : ℕ) (ρ η : ℝ) (OccupancyQuotient BreaksRH : ℕ → Prop),
    1 ≤ a →
      1 < ρ →
        0 < η →
          (∀ b : ℕ, 2 ≤ b → OccupancyQuotient b) →
            (∀ b : ℕ,
              2 ≤ b →
                OccupancyQuotient b →
                  η * ρ ^ (b - 1) > ρ ^ (b / 2) → BreaksRH b) →
              ∃ b0 : ℕ, 2 ≤ b0 ∧ ∀ b : ℕ, b0 ≤ b → BreaksRH b

/-- The second obstruction conclusion: infinite kernel RH requires the linear excitation
threshold, except in the rank-one degeneracy `η = 0`. -/
def pom_occupancy_symquotient_rh_obstruction_linear_threshold_statement : Prop :=
  ∀ (ρ η : ℝ) (b k_b : ℕ),
    1 < ρ →
      0 ≤ η →
        η < ρ →
          (η = 0 ∨
            (0 < η ∧ ((b : ℝ) / 2) * Real.log ρ ≤ (k_b : ℝ) * Real.log (ρ / η))) →
            η = 0 ∨
              ((b : ℝ) / 2) * Real.log ρ / Real.log (ρ / η) ≤ k_b ∧
                (η = Real.sqrt ρ → (b : ℝ) ≤ k_b)

/-- Concrete statement package for the occupancy symmetric-quotient RH obstruction. -/
def pom_occupancy_symquotient_rh_obstruction_statement : Prop :=
  pom_occupancy_symquotient_rh_obstruction_eventual_breaking_statement ∧
    pom_occupancy_symquotient_rh_obstruction_linear_threshold_statement

/-- Paper label: `thm:pom-occupancy-symquotient-rh-obstruction`.

The proof is only the advertised composition: occupancy-only quotients supply first-variation
fidelity for every order, and the excitation-filter theorem isolates the linear-threshold
alternative when `η` is nonzero. -/
theorem paper_pom_occupancy_symquotient_rh_obstruction :
    pom_occupancy_symquotient_rh_obstruction_statement := by
  refine ⟨?_, ?_⟩
  · intro a ρ η OccupancyQuotient BreaksRH ha hρ hη hoccupancy hspectral
    rcases paper_pom_first_variation_fidelity_rh_breaking
        a ρ η OccupancyQuotient BreaksRH ha hρ hη hspectral with
      ⟨b0, hb0, hbreak⟩
    refine ⟨b0, hb0, ?_⟩
    intro b hb
    exact hbreak b hb (hoccupancy b (le_trans hb0 hb))
  · intro ρ η b k_b hρ hη_nonneg hη_lt hη_alt
    rcases hη_alt with hη_zero | hη_pos_bound
    · exact Or.inl hη_zero
    · rcases hη_pos_bound with ⟨hη_pos, hlog_bound⟩
      exact Or.inr
        (paper_pom_excitation_filter_linear_bound ρ η b k_b hρ hη_pos hη_lt hlog_bound)

end Omega.POM
