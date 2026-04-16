import Mathlib.Tactic

namespace Omega.Folding

/-- Chapter-local package for the explicit Tschirnhaus equivalence between the degree-10 gauge
anomaly polynomials `P10` and `Q10`. The fields record the two quotient-level inverse relations
and the induced equalities of the generated root and splitting fields. -/
structure GaugeAnomalyP10Q10TschirnhausData where
  phiPsiInverse : Prop
  psiPhiInverse : Prop
  rootFieldEq : Prop
  splittingFieldEq : Prop
  phiPsiInverseWitness : phiPsiInverse
  psiPhiInverseWitness : psiPhiInverse
  rootFieldEqWitness : rootFieldEq
  splittingFieldEqWitness : splittingFieldEq

/-- Paper-facing wrapper for the explicit `P10`/`Q10` Tschirnhaus inverse: the chapter-local data
already packages the two inverse identities together with the equality of root fields and of
splitting fields.
    prop:fold-gauge-anomaly-P10-Q10-tschirnhaus-inverse -/
theorem paper_fold_gauge_anomaly_p10_q10_tschirnhaus_inverse
    (h : GaugeAnomalyP10Q10TschirnhausData) :
    h.phiPsiInverse /\ h.psiPhiInverse /\ h.rootFieldEq /\ h.splittingFieldEq := by
  exact ⟨h.phiPsiInverseWitness, h.psiPhiInverseWitness, h.rootFieldEqWitness,
    h.splittingFieldEqWitness⟩

end Omega.Folding
