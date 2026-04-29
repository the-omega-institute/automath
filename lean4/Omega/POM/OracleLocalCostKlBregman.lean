import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.POM

/-- Concrete oracle-side package for the local KL/Bregman identity at a hot-phase parameter. -/
structure PomOracleLocalCostKlBregmanData where
  tau : ℝ → ℝ
  tauSlope : ℝ → ℝ
  localCost : ℝ → ℝ
  a : ℝ
  q : ℝ
  paper_label_pom_oracle_local_cost_kl_bregman_a_eq_tauSlope :
    a = tauSlope q
  paper_label_pom_oracle_local_cost_kl_bregman_variational_identity :
    localCost a = tau 1 - tau q - (1 - q) * tauSlope q

namespace PomOracleLocalCostKlBregmanData

/-- Chapter-local Bregman helper associated with the pressure profile `tau`. -/
def paper_label_pom_oracle_local_cost_kl_bregman_localBregman
    (D : PomOracleLocalCostKlBregmanData) (p q : ℝ) : ℝ :=
  D.tau p - D.tau q - D.tauSlope q * (p - q)

lemma paper_label_pom_oracle_local_cost_kl_bregman_localBregman_one
    (D : PomOracleLocalCostKlBregmanData) :
    D.paper_label_pom_oracle_local_cost_kl_bregman_localBregman 1 D.q =
      D.tau 1 - D.tau D.q - (1 - D.q) * D.a := by
  rw [paper_label_pom_oracle_local_cost_kl_bregman_localBregman, ←
    D.paper_label_pom_oracle_local_cost_kl_bregman_a_eq_tauSlope]
  ring

end PomOracleLocalCostKlBregmanData

/-- Paper label: `thm:pom-oracle-local-cost-kl-bregman`. -/
theorem paper_pom_oracle_local_cost_kl_bregman (D : PomOracleLocalCostKlBregmanData) :
    D.localCost D.a = D.tau 1 - D.tau D.q - (1 - D.q) * D.a := by
  calc
    D.localCost D.a = D.tau 1 - D.tau D.q - (1 - D.q) * D.tauSlope D.q :=
      D.paper_label_pom_oracle_local_cost_kl_bregman_variational_identity
    _ = D.tau 1 - D.tau D.q - (1 - D.q) * D.a := by
      rw [← D.paper_label_pom_oracle_local_cost_kl_bregman_a_eq_tauSlope]

end Omega.POM
