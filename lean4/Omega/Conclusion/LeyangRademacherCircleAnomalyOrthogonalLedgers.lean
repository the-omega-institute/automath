import Mathlib.Tactic
import Omega.CircleDimension.StarZ1sDualExtension
import Omega.Conclusion.LeyangFiveBranchBodyAddressRademacherCumulants
import Omega.Conclusion.SerrinWindow6MinimalAnomalyCertificate

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-leyang-rademacher-circle-anomaly-orthogonal-ledgers`.
The Lee--Yang body-fluctuation model is the existing Rademacher cumulant package, while the
continuous visible carrier is one-dimensional and the finite-window anomaly ledger carries `21`
binary coordinates; these carriers are therefore disjoint. -/
theorem paper_conclusion_leyang_rademacher_circle_anomaly_orthogonal_ledgers (n : ℕ) :
    LeyangFiveBranchBodyAddressRademacherCumulants n ∧
      Omega.CircleDimension.circleDim 1 0 = 1 ∧
      Fintype.card Omega.GU.Window6ParityCoordinate = 21 ∧
      (21 : ℕ) = 3 + 18 ∧
      Omega.CircleDimension.circleDim 1 0 ≠ Fintype.card Omega.GU.Window6ParityCoordinate := by
  have hRad := paper_conclusion_leyang_five_branch_body_address_rademacher_cumulants n
  let paper_conclusion_leyang_rademacher_circle_anomaly_orthogonal_ledgers_dual :
      Omega.CircleDimension.Z1sDualExtensionData := { S := ∅ }
  have hDual :=
    Omega.CircleDimension.paper_cdim_star_z1s_dual_extension
      paper_conclusion_leyang_rademacher_circle_anomaly_orthogonal_ledgers_dual
  have hCircle : Omega.CircleDimension.circleDim 1 0 = 1 := by
    simpa
      [Omega.CircleDimension.Z1sDualExtensionData.circleDimEqOne,
        Omega.CircleDimension.z1sStarCircleDim,
        paper_conclusion_leyang_rademacher_circle_anomaly_orthogonal_ledgers_dual]
      using hDual.2.2
  rcases paper_conclusion_serrin_window6_minimal_anomaly_certificate with
    ⟨_, _, _, _, _, hAnomaly, _, _, _⟩
  have hOrthogonal :
      Omega.CircleDimension.circleDim 1 0 ≠ Fintype.card Omega.GU.Window6ParityCoordinate := by
    rw [hCircle, hAnomaly]
    decide
  exact ⟨hRad, hCircle, hAnomaly, by omega, hOrthogonal⟩

end Omega.Conclusion
