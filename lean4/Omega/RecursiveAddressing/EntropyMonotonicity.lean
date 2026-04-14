import Mathlib.Data.Real.Basic

namespace Omega.RecursiveAddressing

set_option maxHeartbeats 400000 in
/-- Paper-facing seed: metric entropy cannot increase under a factor map.
    cor:entropy-monotonicity -/
theorem paper_scan_projection_address_entropy_monotonicity_seeds
    {System : Type}
    (entropy : System → ℝ) (FactorsTo : System → System → Prop)
    (hmono : ∀ {source target : System}, FactorsTo source target → entropy target ≤ entropy source)
    {source target : System} (hfactor : FactorsTo source target) :
    entropy target ≤ entropy source :=
  hmono hfactor

set_option maxHeartbeats 400000 in
/-- Packaged form of the entropy-monotonicity seed.
    cor:entropy-monotonicity -/
theorem paper_scan_projection_address_entropy_monotonicity_package
    {System : Type}
    (entropy : System → ℝ) (FactorsTo : System → System → Prop)
    (hmono : ∀ {source target : System}, FactorsTo source target → entropy target ≤ entropy source)
    {source target : System} (hfactor : FactorsTo source target) :
    entropy target ≤ entropy source :=
  paper_scan_projection_address_entropy_monotonicity_seeds entropy FactorsTo hmono hfactor

end Omega.RecursiveAddressing
