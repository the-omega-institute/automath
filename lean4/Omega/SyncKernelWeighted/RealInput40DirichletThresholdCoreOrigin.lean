import Mathlib

namespace Omega.SyncKernelWeighted

noncomputable section

/-- Concrete data for the factorization `Δ(z,u) = (1 - u z^2) F(z,u)` at the distinguished atom
root and at a threshold mode. The threshold witness has spectral radius strictly bigger than one,
so it cannot come from the atom factor once `|u| = 1`. -/
structure RealInput40DirichletThresholdCoreOriginData where
  u : ℂ
  coreFactor : ℂ → ℂ
  atomRoot : ℂ
  thresholdRoot : ℂ
  hu_unit : ‖u‖ = 1
  hatomRoot : 1 - u * atomRoot ^ 2 = 0
  hthresholdRadius : 1 < ‖thresholdRoot‖
  hthresholdFactorization :
    (1 - u * thresholdRoot ^ 2) * coreFactor thresholdRoot = 0

namespace RealInput40DirichletThresholdCoreOriginData

/-- The distinguished atom-factor root lies on the unit circle. -/
def atomRootsOnUnitCircle (D : RealInput40DirichletThresholdCoreOriginData) : Prop :=
  ‖D.atomRoot‖ = 1

/-- Any threshold mode with spectral radius larger than one must come from the core factor. -/
def thresholdModesComeFromCore (D : RealInput40DirichletThresholdCoreOriginData) : Prop :=
  D.coreFactor D.thresholdRoot = 0

end RealInput40DirichletThresholdCoreOriginData

open RealInput40DirichletThresholdCoreOriginData

lemma atom_factor_root_norm_one {u z : ℂ} (hu : ‖u‖ = 1) (hz : 1 - u * z ^ 2 = 0) :
    ‖z‖ = 1 := by
  have hEq : u * z ^ 2 = 1 := (sub_eq_zero.mp hz).symm
  have hNorm : ‖u * z ^ 2‖ = (1 : ℝ) := by
    simpa using congrArg norm hEq
  have hSq : ‖z‖ ^ 2 = 1 := by
    simpa [hu, norm_mul, norm_pow] using hNorm
  have hz_nonneg : 0 ≤ ‖z‖ := norm_nonneg z
  nlinarith

/-- Factor the Dirichlet threshold polynomial as `(1 - u z^2) F(z,u)`, use `|u| = 1` to place
every atom-factor root on the unit circle, and conclude that a threshold mode with spectral radius
greater than one must come from the core factor.
    thm:killo-real-input-40-dirichlet-threshold-core-origin -/
theorem paper_killo_real_input_40_dirichlet_threshold_core_origin
    (h : RealInput40DirichletThresholdCoreOriginData) :
    h.atomRootsOnUnitCircle ∧ h.thresholdModesComeFromCore := by
  refine ⟨?_, ?_⟩
  · exact atom_factor_root_norm_one h.hu_unit h.hatomRoot
  · rcases mul_eq_zero.mp h.hthresholdFactorization with hAtom | hCore
    · have hUnit : ‖h.thresholdRoot‖ = 1 := atom_factor_root_norm_one h.hu_unit hAtom
      linarith [h.hthresholdRadius]
    · exact hCore

end

end Omega.SyncKernelWeighted
