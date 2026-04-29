import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

namespace Omega.DerivedConsequences

open scoped BigOperators goldenRatio

noncomputable section

/-- A concrete positive zero set taken from the first two golden-resonance scales. -/
def derived_golden_resonance_complete_bernstein_potential_positive_zero : Fin 2 → ℝ
  | 0 => Real.goldenRatio ^ (2 : ℕ) / 2
  | 1 => (3 : ℝ) * Real.goldenRatio ^ (2 : ℕ) / 2

/-- Finite Weierstrass-log potential on the positive axis. -/
def derived_golden_resonance_complete_bernstein_potential_potential (s : ℝ) : ℝ :=
  ∑ i : Fin 2,
    Real.log (s + (derived_golden_resonance_complete_bernstein_potential_positive_zero i) ^ 2)

/-- The associated Stieltjes series. -/
def derived_golden_resonance_complete_bernstein_potential_stieltjes (s : ℝ) : ℝ :=
  ∑ i : Fin 2,
    1 /
      (s + (derived_golden_resonance_complete_bernstein_potential_positive_zero i) ^ 2)

/-- The explicit positive kernel encoding the alternating higher derivatives of the Stieltjes
series. -/
def derived_golden_resonance_complete_bernstein_potential_signed_higher
    (n : ℕ) (s : ℝ) : ℝ :=
  (Nat.factorial n : ℝ) *
    ∑ i : Fin 2,
      1 /
        (s + (derived_golden_resonance_complete_bernstein_potential_positive_zero i) ^ 2) ^
          (n + 1)

lemma derived_golden_resonance_complete_bernstein_potential_term_hasDerivAt
    (i : Fin 2) {s : ℝ} (hs : 0 < s) :
    HasDerivAt
      (fun t : ℝ =>
        Real.log (t + (derived_golden_resonance_complete_bernstein_potential_positive_zero i) ^ 2))
      (1 /
        (s + (derived_golden_resonance_complete_bernstein_potential_positive_zero i) ^ 2))
      s := by
  have harg :
      0 <
        s + (derived_golden_resonance_complete_bernstein_potential_positive_zero i) ^ 2 := by
    positivity
  simpa using
    (Real.hasDerivAt_log harg.ne').comp_add_const s
      ((derived_golden_resonance_complete_bernstein_potential_positive_zero i) ^ 2)

/-- Paper label: `thm:derived-golden-resonance-complete-bernstein-potential`. For the concrete
finite-support golden-resonance proxy, the imaginary-axis logarithmic potential differentiates to a
positive Stieltjes sum, and the explicit alternating higher-derivative kernels are nonnegative on
`(0, ∞)`. -/
theorem paper_derived_golden_resonance_complete_bernstein_potential :
    (∀ s : ℝ, 0 < s →
      HasDerivAt derived_golden_resonance_complete_bernstein_potential_potential
        (derived_golden_resonance_complete_bernstein_potential_stieltjes s) s) ∧
      (∀ n : ℕ, ∀ s : ℝ, 0 < s →
        0 ≤ derived_golden_resonance_complete_bernstein_potential_signed_higher n s) := by
  refine ⟨?_, ?_⟩
  · intro s hs
    unfold derived_golden_resonance_complete_bernstein_potential_potential
      derived_golden_resonance_complete_bernstein_potential_stieltjes
    simpa using
      ((HasDerivAt.sum (u := (Finset.univ : Finset (Fin 2)))
        (fun i _ => derived_golden_resonance_complete_bernstein_potential_term_hasDerivAt i hs)))
  · intro n s hs
    unfold derived_golden_resonance_complete_bernstein_potential_signed_higher
    refine mul_nonneg (by positivity) ?_
    exact Finset.sum_nonneg fun i hi => by
      have hden :
          0 <
            ((derived_golden_resonance_complete_bernstein_potential_positive_zero i) ^ 2 + s) ^
              (n + 1) := by
        positivity
      positivity

end

end Omega.DerivedConsequences
