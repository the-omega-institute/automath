import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Folding.KilloFoldBinEscortRenyiLogisticGeometry

namespace Omega.Folding

/-- Concrete data for the escort-to-escort KL package: two temperatures `p,q ≥ 0` together with
the Bernoulli closed form extracted from the last-bit escort reduction. -/
structure FoldBinEscortEscortKlData where
  p : ℝ
  q : ℝ
  hp : 0 ≤ p
  hq : 0 ≤ q

namespace FoldBinEscortEscortKlData

/-- The last-bit escort asymptotic written as the closed Bernoulli KL expression. -/
noncomputable def klLimit (D : FoldBinEscortEscortKlData) : ℝ :=
  killoEscortTheta D.q * Real.log (killoEscortTheta D.q / killoEscortTheta D.p) +
    (1 - killoEscortTheta D.q) * Real.log ((1 - killoEscortTheta D.q) / (1 - killoEscortTheta D.p))

end FoldBinEscortEscortKlData

/-- Paper label: `prop:fold-bin-escort-escort-kl`. The last-bit escort reduction turns the
temperature-to-temperature KL limit into the Bernoulli closed form already verified for the escort
logistic geometry. -/
theorem paper_fold_bin_escort_escort_kl (D : FoldBinEscortEscortKlData) :
    D.klLimit = killoEscortKLDivergence D.p D.q := by
  simpa [FoldBinEscortEscortKlData.klLimit] using
    (paper_killo_fold_bin_escort_renyi_logistic_geometry.2.1 D.p D.q D.hp D.hq).symm

end Omega.Folding
