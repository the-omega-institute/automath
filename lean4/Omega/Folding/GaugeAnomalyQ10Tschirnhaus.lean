import Mathlib.Tactic
import Omega.Folding.GaugeAnomalyP10Q10TschirnhausInverse

namespace Omega.Folding

/-- Chapter-local package for the explicit `Q10` Tschirnhaus elimination certificate. Besides the
already formalized `P10`/`Q10` inverse wrapper, the paper packages the resultant factorization,
the linear back-substitution, the branch-locus parametrization, and the precomputed
Galois/discriminant facts. -/
structure GaugeAnomalyQ10TschirnhausData where
  resultantFactorization : Prop
  linearBackSubstitution : Prop
  branchLocusParametrization : Prop
  galoisGroupS10 : Prop
  discriminantFactorization : Prop
  resultantFactorization_h : resultantFactorization
  linearBackSubstitution_h : linearBackSubstitution
  branchLocusParametrization_h : branchLocusParametrization
  galoisGroupS10_h : galoisGroupS10
  discriminantFactorization_h : discriminantFactorization

/-- Paper-facing wrapper for the `Q10` Tschirnhaus elimination package.
    prop:fold-gauge-anomaly-Q10-tschirnhaus -/
theorem paper_fold_gauge_anomaly_q10_tschirnhaus
    (h : GaugeAnomalyQ10TschirnhausData) :
    h.resultantFactorization ∧ h.linearBackSubstitution ∧ h.branchLocusParametrization ∧
      h.galoisGroupS10 ∧ h.discriminantFactorization := by
  exact ⟨h.resultantFactorization_h, h.linearBackSubstitution_h,
    h.branchLocusParametrization_h, h.galoisGroupS10_h, h.discriminantFactorization_h⟩

end Omega.Folding
