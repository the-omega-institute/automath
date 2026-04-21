import Mathlib
import Omega.Conclusion.CapacityMajorizationSchurHardness

namespace Omega.Folding

open Omega.Conclusion

/-- Concrete finite-spectrum package for the capacity/majorization equivalence. -/
structure FoldCapacityOrderMajorizationData where
  d : List ℝ
  e : List ℝ

namespace FoldCapacityOrderMajorizationData

/-- Capacity dominance written as pointwise comparison of the truncated-mass curves together with
the common total mass hypothesis from the paper statement. -/
def capacityDominance (D : FoldCapacityOrderMajorizationData) : Prop :=
  (∀ T : ℝ, capacityCurve D.d T ≤ capacityCurve D.e T) ∧ D.d.sum = D.e.sum

/-- Majorization order in the Hardy-Littlewood-Polya tail-sum form, with the same total mass. -/
def majorizationOrder (D : FoldCapacityOrderMajorizationData) : Prop :=
  majorizes D.d D.e ∧ D.d.sum = D.e.sum

lemma capacityDominance_iff_majorizationOrder (D : FoldCapacityOrderMajorizationData) :
    D.capacityDominance ↔ D.majorizationOrder := by
  constructor
  · rintro ⟨hcap, hmass⟩
    refine ⟨?_, hmass⟩
    simpa using (paper_conclusion_capacity_majorization_schur_hardness D.d D.e).2 hcap
  · rintro ⟨hmaj, hmass⟩
    refine ⟨?_, hmass⟩
    simpa using (paper_conclusion_capacity_majorization_schur_hardness D.d D.e).1 hmaj

end FoldCapacityOrderMajorizationData

open FoldCapacityOrderMajorizationData

/-- Paper label: `thm:fold-capacity-order-majorization-equivalence`. -/
theorem paper_fold_capacity_order_majorization_equivalence
    (D : FoldCapacityOrderMajorizationData) :
    D.capacityDominance ↔ D.majorizationOrder := by
  simpa using D.capacityDominance_iff_majorizationOrder

end Omega.Folding
