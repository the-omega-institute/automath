import Mathlib.Tactic
import Omega.Experiments.ParryBaselineGapSturmian
import Omega.Experiments.TVCertificateHist

namespace Omega.POM

/-- Combining the folded-histogram triangle step with the Sturmian-vs-Parry gap yields a direct
empirical lower bound on the Parry-complexity detector. -/
theorem paper_pom_parry_complexity_detector (m : Nat) (tvEmpParry tvFoldParry star
    zeroCylinderMass : Real)
    (hTriangle : tvFoldParry ≤ tvEmpParry + (m + 1 : Real) * star)
    (hGap : 1 - (m + 1 : Real) * zeroCylinderMass ≤ tvFoldParry) :
    1 - (m + 1 : Real) * zeroCylinderMass - (m + 1 : Real) * star ≤ tvEmpParry := by
  have hFoldUpper : tvFoldParry ≤ (m + 1 : Real) * star + tvEmpParry := by
    obtain ⟨_, _, hUpper⟩ :=
      Omega.Experiments.TVCertificateHist.paper_tv_decomposition_parry m
        ((m + 1 : Real) * star) ((m + 1 : Real) * star) tvFoldParry tvEmpParry star le_rfl le_rfl
        (by simpa [add_comm, add_left_comm, add_assoc] using hTriangle)
    simpa [add_comm, add_left_comm, add_assoc] using hUpper
  have hFoldLower : 1 - (m + 1 : Real) * zeroCylinderMass ≤ tvFoldParry := by
    simpa using
      Omega.Experiments.ParryBaselineGapSturmian.paper_parry_baseline_gap_sturmian m
        tvFoldParry ((m + 1 : Real) * zeroCylinderMass) zeroCylinderMass le_rfl hGap
  linarith

end Omega.POM
