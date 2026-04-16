import Mathlib.Tactic

namespace Omega.CircleDimension

/-- Chapter-local integer-matrix rank data for a Borel measurable torus homomorphism whose source
rank strictly exceeds its target rank. The lower bound on `kernelRank` models the positive
dimension forced by rank drop, while injectivity would force the kernel to be trivial. -/
structure BorelHomomorphismNoncollapseData where
  sourceRank : ℕ
  targetRank : ℕ
  kernelRank : ℕ
  rankDrop : targetRank < sourceRank
  kernelLowerBound : sourceRank - targetRank ≤ kernelRank
  existsInjectiveBorelHom : Prop
  injectiveImpliesKernelZero : existsInjectiveBorelHom → kernelRank = 0

/-- A Borel measurable torus homomorphism cannot stay injective when the source rank exceeds the
target rank: the induced integer-matrix model has positive-dimensional kernel.
    prop:cdim-borel-homomorphism-noncollapse -/
theorem paper_cdim_borel_homomorphism_noncollapse (h : BorelHomomorphismNoncollapseData) :
    ¬ h.existsInjectiveBorelHom := by
  intro hinj
  have hgap : 0 < h.sourceRank - h.targetRank := Nat.sub_pos_of_lt h.rankDrop
  have hker_ge_one : 1 ≤ h.kernelRank := by
    exact le_trans (Nat.succ_le_iff.mpr hgap) h.kernelLowerBound
  have hker_pos : 0 < h.kernelRank := by
    simpa using hker_ge_one
  have hker_zero : h.kernelRank = 0 := h.injectiveImpliesKernelZero hinj
  omega

end Omega.CircleDimension
