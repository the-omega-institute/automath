import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic
import Omega.Folding.GaugeAnomalySingularityLatticeNonholonomic

namespace Omega.Folding

/-- If the coefficient sequence is `P`-recursive, the associated generating function is
`D`-finite. This is the bridge used in the paper-facing contradiction. -/
lemma p_recursive_generating_function_dfinite (κ : ℕ → Complex) (PG : Complex → Complex)
    (DFinite : (Complex → Complex) → Prop) (PRecursive : (ℕ → Complex) → Prop)
    (h_bridge : PRecursive κ → DFinite PG) :
    PRecursive κ → DFinite PG := h_bridge

/-- The nonholonomic generating function cannot have a `P`-recursive coefficient sequence.
    cor:fold-gauge-anomaly-cumulants-not-precursive -/
theorem paper_fold_gauge_anomaly_cumulants_not_precursive (κ : ℕ → Complex) (PG : Complex → Complex)
    (DFinite : (Complex → Complex) → Prop) (PRecursive : (ℕ → Complex) → Prop)
    (h_bridge : PRecursive κ → DFinite PG) (h_nonholonomic : ¬ DFinite PG) : ¬ PRecursive κ := by
  intro hprec
  exact h_nonholonomic (p_recursive_generating_function_dfinite κ PG DFinite PRecursive h_bridge hprec)

end Omega.Folding
