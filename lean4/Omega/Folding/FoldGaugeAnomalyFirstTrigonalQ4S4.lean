import Mathlib.Algebra.Polynomial.Basic
import Omega.Folding.GaugeAnomalyTrigonalQ4Galois

namespace Omega.Folding

open Polynomial

noncomputable section

/-- The paper's first-trigonal quartic `Q(t)` is the audited `q₄`. -/
def foldGaugeAnomalyFirstTrigonalQ4 : Polynomial ℤ :=
  q4

/-- The mod-`17` irreducibility certificate used in the quartic Galois audit. -/
def foldGaugeAnomalyFirstTrigonalQ4Irreducible : Prop :=
  q4Mod17FactorDegrees = [4]

/-- Paper-facing wrapper around the audited first-trigonal quartic certificate. -/
def FoldGaugeAnomalyFirstTrigonalQ4S4Statement : Prop :=
  foldGaugeAnomalyFirstTrigonalQ4 = 9 * X ^ 4 - 6 * X ^ 3 + 4 * X ^ 2 + 8 * X - 16 ∧
    foldGaugeAnomalyFirstTrigonalQ4Irreducible ∧
    q4Discriminant = -(2 ^ 12) * 3 ^ 4 * 1931 ∧
    q4GaloisGroup = QuarticTransitiveSubgroup.s4 ∧
    q4DiscriminantIsNonsquare

/-- Paper label: `prop:fold-gauge-anomaly-first-trigonal-q4-s4`. -/
theorem paper_fold_gauge_anomaly_first_trigonal_q4_s4 :
    FoldGaugeAnomalyFirstTrigonalQ4S4Statement := by
  rcases paper_fold_gauge_anomaly_trigonal_q4_galois with
    ⟨hq4, hdisc, hmod17, _hmod13, hgalois, _hquad, hnonsquare⟩
  exact ⟨hq4, hmod17, hdisc, hgalois, hnonsquare⟩

end

end Omega.Folding
