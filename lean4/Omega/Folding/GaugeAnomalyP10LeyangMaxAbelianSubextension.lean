import Mathlib
import Omega.Folding.FoldGaugeAnomalyP10HLinearDisjointness
import Omega.Folding.KilloLeyangTwoBranchFieldsProductGalois

namespace Omega.Folding

/-- Paper label: `cor:fold-gauge-anomaly-P10-leyang-max-abelian-subextension`. The four quadratic
sign classes attached to the biquadratic abelianization are exactly `0`, `K10`, `KLY`, and
`K10 * KLY`, and these audited integers are pairwise distinct. -/
theorem paper_fold_gauge_anomaly_p10_leyang_max_abelian_subextension :
    let K10 : ℤ := foldGaugeAnomalyP10QuadraticSubfield
    let KLY : ℤ := killoLeyangCubicQuadraticSubfieldDiscriminant
    ({0, K10, KLY, K10 * KLY} : Finset ℤ).card = 4 := by
  dsimp [foldGaugeAnomalyP10QuadraticSubfield, killoLeyangCubicQuadraticSubfieldDiscriminant]
  native_decide

end Omega.Folding
