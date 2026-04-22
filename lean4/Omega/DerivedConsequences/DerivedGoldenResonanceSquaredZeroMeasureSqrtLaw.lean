import Mathlib.Tactic
import Omega.DerivedConsequences.DerivedGoldenResonanceCompleteBernsteinPotential

namespace Omega.DerivedConsequences

open scoped BigOperators goldenRatio

noncomputable section

/-- The finite Stieltjes sum viewed as the discrete squared-zero measure integral. -/
def derived_golden_resonance_squared_zero_measure_sqrt_law_stieltjes_sum (s : ℝ) : ℝ :=
  ∑ i : Fin 2,
    1 / (s + (derived_golden_resonance_complete_bernstein_potential_positive_zero i) ^ 2)

/-- Distribution function of the squared positive-zero measure for the concrete two-point model. -/
def derived_golden_resonance_squared_zero_measure_sqrt_law_distribution (R : ℝ) : ℕ :=
  (Finset.univ.filter fun i : Fin 2 =>
    (derived_golden_resonance_complete_bernstein_potential_positive_zero i) ^ 2 ≤ R).card

/-- Positive-zero counting function for the same concrete two-point model. -/
def derived_golden_resonance_squared_zero_measure_sqrt_law_positive_zero_count (R : ℝ) : ℕ :=
  (Finset.univ.filter fun i : Fin 2 =>
    derived_golden_resonance_complete_bernstein_potential_positive_zero i ≤ R).card

private lemma derived_golden_resonance_squared_zero_measure_sqrt_law_positive_zero_nonneg
    (i : Fin 2) :
    0 ≤ derived_golden_resonance_complete_bernstein_potential_positive_zero i := by
  fin_cases i
  · have hphi : 0 < Real.goldenRatio := Real.goldenRatio_pos
    change 0 ≤ Real.goldenRatio ^ (2 : ℕ) / 2
    positivity
  · have hphi : 0 < Real.goldenRatio := Real.goldenRatio_pos
    change 0 ≤ (3 : ℝ) * Real.goldenRatio ^ (2 : ℕ) / 2
    positivity

/-- Paper label: `cor:derived-golden-resonance-squared-zero-measure-sqrt-law`.
The complete-Bernstein derivative is exactly the finite Stieltjes sum over the squared positive
zeros, and the distribution function of the squared-zero measure is the positive-zero counting
function evaluated at `sqrt R`. -/
theorem paper_derived_golden_resonance_squared_zero_measure_sqrt_law :
    (∀ s : ℝ, 0 < s →
      HasDerivAt derived_golden_resonance_complete_bernstein_potential_potential
        (derived_golden_resonance_complete_bernstein_potential_stieltjes s) s) ∧
      (∀ s : ℝ,
        derived_golden_resonance_squared_zero_measure_sqrt_law_stieltjes_sum s =
          derived_golden_resonance_complete_bernstein_potential_stieltjes s) ∧
      (∀ R : ℝ, 0 ≤ R →
        derived_golden_resonance_squared_zero_measure_sqrt_law_distribution R =
          derived_golden_resonance_squared_zero_measure_sqrt_law_positive_zero_count
            (Real.sqrt R)) := by
  refine ⟨paper_derived_golden_resonance_complete_bernstein_potential.1, ?_, ?_⟩
  · intro s
    rfl
  · intro R hR
    have hsq :
        ∀ i : Fin 2,
          (derived_golden_resonance_complete_bernstein_potential_positive_zero i) ^ 2 ≤ R ↔
            derived_golden_resonance_complete_bernstein_potential_positive_zero i ≤ Real.sqrt R := by
      intro i
      have hpos :
          0 ≤ derived_golden_resonance_complete_bernstein_potential_positive_zero i := by
        exact
          derived_golden_resonance_squared_zero_measure_sqrt_law_positive_zero_nonneg i
      have hsqrt_nonneg : 0 ≤ Real.sqrt R := Real.sqrt_nonneg R
      constructor
      · intro hle
        nlinarith [hle, Real.sq_sqrt hR, hsqrt_nonneg]
      · intro hle
        nlinarith [hle, Real.sq_sqrt hR, hsqrt_nonneg]
    simp [derived_golden_resonance_squared_zero_measure_sqrt_law_distribution,
      derived_golden_resonance_squared_zero_measure_sqrt_law_positive_zero_count, hsq]

end

end Omega.DerivedConsequences
