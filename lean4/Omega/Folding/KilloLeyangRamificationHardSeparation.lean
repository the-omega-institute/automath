import Mathlib.Tactic
import Omega.Folding.FoldGaugeAnomalyP10UniqueQuadraticSubfield
import Omega.Folding.KilloLeyangTwoBranchFieldsProductGalois
import Omega.Zeta.XiTerminalZmKappaSquareCubicFieldS3

namespace Omega.Folding

/-- Concrete `P10` discriminant package used for the ramification comparison. -/
def killo_leyang_ramification_hard_separation_p10_data : FoldGaugeAnomalyP10GaloisDiscriminantData :=
  {}

/-- The ramification intersection is forced away from `37` on the `P10` side. -/
def killo_leyang_ramification_hard_separation_statement : Prop :=
  FoldGaugeAnomalyP10GaloisDiscriminantData.fold_gauge_anomaly_p10_galois_discriminant_squarefree_kernel
      killo_leyang_ramification_hard_separation_p10_data =
      66269989 ∧
    ¬ (37 : ℤ) ∣
      FoldGaugeAnomalyP10GaloisDiscriminantData.fold_gauge_anomaly_p10_galois_discriminant_squarefree_kernel
        killo_leyang_ramification_hard_separation_p10_data ∧
    Omega.Zeta.xiTerminalKappaSquareDiscriminant =
      -((2 : ℤ) ^ 6 * (3 : ℤ) ^ 9 * 37) ∧
    (37 : ℤ) ∣ Omega.Zeta.xiTerminalKappaSquareDiscriminant ∧
    (killoLeyangTenQuadraticRamificationPrimes ∩ killoLeyangCubicQuadraticRamificationPrimes) ⊆
      ({3} : Finset ℕ)

/-- Paper label: `prop:killo-leyang-ramification-hard-separation`. The Lee--Yang cubic
discriminant is visibly ramified at `37`, while the `P10` quadratic discriminant kernel is
`66269989 = 1931 * 34319`, so `37` does not occur on the `P10` side. Hence the common
ramification support is contained in `{3}`. -/
theorem paper_killo_leyang_ramification_hard_separation :
    killo_leyang_ramification_hard_separation_statement := by
  rcases paper_fold_gauge_anomaly_p10_unique_quadratic_subfield
      killo_leyang_ramification_hard_separation_p10_data with ⟨_, _, hk⟩
  rcases Omega.Zeta.paper_xi_terminal_zm_kappa_square_cubic_field_s3 with ⟨_, _, _, hdisc, _⟩
  refine ⟨hk, ?_, hdisc, ?_, ?_⟩
  · rw [hk]
    norm_num
  · refine ⟨-((2 : ℤ) ^ 6 * (3 : ℤ) ^ 9), ?_⟩
    rw [hdisc]
    ring
  · native_decide

end Omega.Folding
