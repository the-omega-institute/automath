import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Algebra.Field
import Omega.Conclusion.BinfoldRenyiRateCollapse
import Omega.Folding.FoldBinEscortEscortKl
import Omega.Zeta.XiFoldbinEscortTvCollapseOnebitGibbs

namespace Omega.Conclusion

open Filter

noncomputable section

/-- Concrete marker for the fixed-temperature one-bit fold information-geometry package. -/
abbrev conclusion_fold_onebit_information_geometry_collapse_data := Unit

namespace conclusion_fold_onebit_information_geometry_collapse_data

/-- The finite escort family collapses in total variation to its one-bit Gibbs limit. -/
def tv_collapse (_D : conclusion_fold_onebit_information_geometry_collapse_data) : Prop :=
  Omega.Zeta.xi_foldbin_escort_tv_collapse_onebit_gibbs_statement

/-- The two-temperature KL limit is the Bernoulli KL formula on the escort logistic curve. -/
def kl_bernoulli_limit
    (_D : conclusion_fold_onebit_information_geometry_collapse_data) : Prop :=
  ∀ p q : ℝ, 0 ≤ p → 0 ≤ q →
    Omega.Folding.killoEscortKLDivergence p q =
      Omega.Folding.killoEscortTheta q *
          Real.log
            (Omega.Folding.killoEscortTheta q / Omega.Folding.killoEscortTheta p) +
        (1 - Omega.Folding.killoEscortTheta q) *
          Real.log
            ((1 - Omega.Folding.killoEscortTheta q) /
              (1 - Omega.Folding.killoEscortTheta p))

/-- Fixed Renyi orders share the sublinear normalized rate encoded by the bin-fold entropy
collapse. -/
def renyi_sublinear_rates
    (_D : conclusion_fold_onebit_information_geometry_collapse_data) : Prop :=
  ∀ q : ℝ, 0 < q →
    Tendsto (Omega.Folding.foldBinRenyiEntropyRate q) atTop
      (nhds (Real.log Real.goldenRatio))

end conclusion_fold_onebit_information_geometry_collapse_data

/-- Paper label: `thm:conclusion-fold-onebit-information-geometry-collapse`. -/
theorem paper_conclusion_fold_onebit_information_geometry_collapse
    (D : conclusion_fold_onebit_information_geometry_collapse_data) :
    D.tv_collapse ∧ D.kl_bernoulli_limit ∧ D.renyi_sublinear_rates := by
  refine ⟨Omega.Zeta.paper_xi_foldbin_escort_tv_collapse_onebit_gibbs, ?_, ?_⟩
  · intro p q hp hq
    exact (Omega.Folding.paper_killo_fold_bin_escort_renyi_logistic_geometry.2.1 p q hp hq)
  · intro q hq
    exact paper_conclusion_binfold_renyi_rate_collapse q hq

end

end Omega.Conclusion
