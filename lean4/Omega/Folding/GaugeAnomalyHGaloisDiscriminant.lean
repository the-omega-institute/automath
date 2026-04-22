import Mathlib
import Omega.Folding.FoldGaugeAnomalyP10HLinearDisjointness
import Omega.Folding.GaugeAnomalyQ19GaloisS19

namespace Omega.Folding

open Polynomial
open Omega.Folding.GaugeAnomalyQ19

/-- Chapter-local name for the degree-`19` squarefactor polynomial `H(u)` appearing in the
rate-curve discriminant certificate. -/
noncomputable def fold_gauge_anomaly_h_galois_discriminant_polynomial : ℤ[X] :=
  Q19

/-- The audited mod-`73` factorization pattern for `H(u)`. -/
def fold_gauge_anomaly_h_galois_discriminant_mod73_factor_degrees : List ℕ :=
  q19Mod73FactorDegrees

/-- The audited mod-`17` factorization pattern for `H(u)`. -/
def fold_gauge_anomaly_h_galois_discriminant_mod17_factor_degrees : List ℕ :=
  q19Mod17FactorDegrees

/-- The mod-`13` discriminant residue used to exclude `A₁₉`. -/
def fold_gauge_anomaly_h_galois_discriminant_mod13_residue : ZMod 13 :=
  q19DiscriminantMod13

/-- Paper label: `prop:fold-gauge-anomaly-H-galois-discriminant`. The degree-`19` squarefactor
`H(u)` is the audited polynomial `Q₁₉(u)`: the mod-`73` certificate gives irreducibility, the
mod-`17` certificate contributes an `11`-cycle, the mod-`13` discriminant residue excludes `A₁₉`,
and the existing rate-curve factorization records the discriminant contribution of `H(u)^2`. -/
theorem paper_fold_gauge_anomaly_h_galois_discriminant :
    fold_gauge_anomaly_h_galois_discriminant_polynomial = Q19 ∧
      fold_gauge_anomaly_h_galois_discriminant_mod73_factor_degrees = [19] ∧
      fold_gauge_anomaly_h_galois_discriminant_mod17_factor_degrees = [11, 8] ∧
      fold_gauge_anomaly_h_galois_discriminant_mod13_residue = 8 ∧
      q19IrreducibleOverQ ∧
      q19ContainsElevenCycle ∧
      q19GaloisGroupIsFullSymmetric ∧
      DiscAlphaR =
        -(X ^ 11 : ℤ[X]) * (X - 1) * P10 * fold_gauge_anomaly_h_galois_discriminant_polynomial ^ 2 ∧
      foldGaugeAnomalyHSplittingDegree = Nat.factorial 19 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, paper_fold_gauge_anomaly_q19_galois_s19, ?_, rfl⟩
  simpa [fold_gauge_anomaly_h_galois_discriminant_polynomial] using
    paper_fold_gauge_anomaly_rate_curve_disc_factorization_q19

end Omega.Folding
