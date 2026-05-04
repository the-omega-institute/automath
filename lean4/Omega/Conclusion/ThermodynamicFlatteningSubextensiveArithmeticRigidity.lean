import Mathlib.Tactic
import Omega.Conclusion.BernoulliZetaTowerExplicitTriangularInversion
import Omega.Folding.FoldBinGaugeConstantStirlingBernoulliHierarchy
import Omega.Folding.FoldBinRenyiRateCollapse

open Filter

namespace Omega.Conclusion

/-- Concrete data for the triangular recovery layer used by the conclusion wrapper. -/
structure conclusion_thermodynamic_flattening_subextensive_arithmetic_rigidity_data where
  conclusion_thermodynamic_flattening_subextensive_arithmetic_rigidity_coefficientRecovered :
    ℕ → Prop
  conclusion_thermodynamic_flattening_subextensive_arithmetic_rigidity_bernoulliRecovered :
    ℕ → Prop
  conclusion_thermodynamic_flattening_subextensive_arithmetic_rigidity_zetaRecovered :
    ℕ → Prop
  conclusion_thermodynamic_flattening_subextensive_arithmetic_rigidity_step :
    ∀ r, 1 ≤ r →
      (∀ s, 1 ≤ s → s < r →
        conclusion_thermodynamic_flattening_subextensive_arithmetic_rigidity_coefficientRecovered
          s) →
        conclusion_thermodynamic_flattening_subextensive_arithmetic_rigidity_coefficientRecovered
          r
  conclusion_thermodynamic_flattening_subextensive_arithmetic_rigidity_bernoulli :
    ∀ r,
      conclusion_thermodynamic_flattening_subextensive_arithmetic_rigidity_coefficientRecovered
        r →
      conclusion_thermodynamic_flattening_subextensive_arithmetic_rigidity_bernoulliRecovered r
  conclusion_thermodynamic_flattening_subextensive_arithmetic_rigidity_zeta :
    ∀ r,
      conclusion_thermodynamic_flattening_subextensive_arithmetic_rigidity_bernoulliRecovered r →
      conclusion_thermodynamic_flattening_subextensive_arithmetic_rigidity_zetaRecovered r

namespace conclusion_thermodynamic_flattening_subextensive_arithmetic_rigidity_data

/-- Extensional thermodynamic flattening: every positive Rényi order has the same rate. -/
def conclusion_thermodynamic_flattening_subextensive_arithmetic_rigidity_renyiLayer
    (_D : conclusion_thermodynamic_flattening_subextensive_arithmetic_rigidity_data) : Prop :=
  ∀ q : ℝ, 0 < q →
    Tendsto (Omega.Folding.foldBinRenyiEntropyRate q) atTop
      (nhds (Real.log Real.goldenRatio))

/-- Subextensive arithmetic layer: the Stirling--Bernoulli gauge hierarchy is present, and the
even-zeta tower is recovered by triangular inversion. -/
def conclusion_thermodynamic_flattening_subextensive_arithmetic_rigidity_arithmeticLayer
    (D : conclusion_thermodynamic_flattening_subextensive_arithmetic_rigidity_data) : Prop :=
  Omega.Folding.fold_bin_gauge_constant_stirling_bernoulli_hierarchy_statement ∧
    ∀ r, 1 ≤ r →
      D.conclusion_thermodynamic_flattening_subextensive_arithmetic_rigidity_coefficientRecovered
          r ∧
        D.conclusion_thermodynamic_flattening_subextensive_arithmetic_rigidity_bernoulliRecovered
          r ∧
          D.conclusion_thermodynamic_flattening_subextensive_arithmetic_rigidity_zetaRecovered
            r

/-- Paper-facing formulation: the extensional thermodynamic layer and the subextensive arithmetic
layer split as a conjunction. -/
def conclusion_thermodynamic_flattening_subextensive_arithmetic_rigidity_statement
    (D : conclusion_thermodynamic_flattening_subextensive_arithmetic_rigidity_data) : Prop :=
  D.conclusion_thermodynamic_flattening_subextensive_arithmetic_rigidity_renyiLayer ∧
    D.conclusion_thermodynamic_flattening_subextensive_arithmetic_rigidity_arithmeticLayer

end conclusion_thermodynamic_flattening_subextensive_arithmetic_rigidity_data

open conclusion_thermodynamic_flattening_subextensive_arithmetic_rigidity_data

/-- Paper label:
`thm:conclusion-thermodynamic-flattening-subextensive-arithmetic-rigidity`. -/
theorem paper_conclusion_thermodynamic_flattening_subextensive_arithmetic_rigidity
    (D : conclusion_thermodynamic_flattening_subextensive_arithmetic_rigidity_data) :
    conclusion_thermodynamic_flattening_subextensive_arithmetic_rigidity_statement D := by
  refine ⟨?_, ?_⟩
  · intro q hq
    exact Omega.Folding.paper_fold_bin_renyi_rate_collapse q hq
  · refine ⟨Omega.Folding.paper_fold_bin_gauge_constant_stirling_bernoulli_hierarchy, ?_⟩
    exact paper_conclusion_bernoulli_zeta_tower_explicit_triangular_inversion
      D.conclusion_thermodynamic_flattening_subextensive_arithmetic_rigidity_coefficientRecovered
      D.conclusion_thermodynamic_flattening_subextensive_arithmetic_rigidity_bernoulliRecovered
      D.conclusion_thermodynamic_flattening_subextensive_arithmetic_rigidity_zetaRecovered
      D.conclusion_thermodynamic_flattening_subextensive_arithmetic_rigidity_step
      D.conclusion_thermodynamic_flattening_subextensive_arithmetic_rigidity_bernoulli
      D.conclusion_thermodynamic_flattening_subextensive_arithmetic_rigidity_zeta

end Omega.Conclusion
