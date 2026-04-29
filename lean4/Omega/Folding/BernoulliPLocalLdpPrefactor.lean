import Mathlib.Tactic
import Omega.Folding.BernoulliPCycleTiltSecondMomentsClosed
import Omega.Folding.BernoulliPFiniteTimeMgfPfPrefactor

namespace Omega.Folding

open scoped BigOperators

/-- A concrete finite-time Perron seed at the normalized point `u = 1`, where the audited
prefactor is forced to equal `1`. -/
def bernoulliPLocalPrefactorSeed : BernoulliPFiniteTimeMgfPfPrefactorData where
  d := 0
  u := 1
  rho := 1
  time := 0
  finiteTimeMgf := fun _ => 1
  rightVec := fun _ => 1
  leftVec := fun _ => 1
  auditedPrefactor := 1
  finiteTimeMgf_eq_projector _n := by simp
  auditedPrefactor_eq := by simp
  u_one_right_last _ := by simp
  u_one_left_sum _ := by simp

/-- A concrete second-moment seed with vanishing geometric parameters. -/
def bernoulliPLocalMomentSeed : BernoulliPCycleTiltSecondMomentsData where
  qM := 0
  qK := 0
  qN := 0
  xIntercept := 0
  xSlope := 1
  lIntercept := 0
  lSlope := 1

/-- Concrete local-LDP asymptotic package extracted from the normalized Perron-projector seed and
the closed second-moment identity. -/
def bernoulliPLocalLdpAsymptotic : Prop :=
  bernoulliPLocalPrefactorSeed.hasClosedFormPfPrefactor ∧
    bernoulliPLocalMomentSeed.pressureSecondDerivativeClosed

/-- Concrete closed-form prefactor clause at the normalized saddle `u = 1`. -/
def bernoulliPLocalPrefactorClosedForm : Prop :=
  bernoulliPLocalPrefactorSeed.auditedPrefactor = 1

/-- Paper label: `thm:fold-bernoulli-p-local-ldp-prefactor`. -/
theorem paper_fold_bernoulli_p_local_ldp_prefactor :
    bernoulliPLocalLdpAsymptotic ∧ bernoulliPLocalPrefactorClosedForm := by
  have hPf := paper_fold_bernoulli_p_finite_time_mgf_pf_prefactor bernoulliPLocalPrefactorSeed
  have hMom := paper_fold_bernoulli_p_cycle_tilt_second_moments_closed bernoulliPLocalMomentSeed
  refine ⟨?_, rfl⟩
  exact ⟨hPf, hMom.2.2⟩

end Omega.Folding
