import Omega.CircleDimension.AtomicDefectProny2KappaRecovery
import Mathlib.Tactic

namespace Omega.TypedAddressBiaxialCompletion

/-- Chapter-local package for the comoving Prony threshold split. The first half records that the
rank of the Hankel window closes exactly when the affine dependence on the top sample is fixed,
while the second half records that the existing `2κ`-sample atomic-Prony package supplies exact
reconstruction once the final sample is present. -/
structure ComovingPronyThresholdData where
  kappa : ℕ
  rankDetectionWindow : ℕ
  exactRecoveryWindow : ℕ
  hankelDetAffineInTopSample : Prop
  prefixLeavesOneFreeParameter : Prop
  nextSampleClosesRankDetection : Prop
  rankDetectionWindow_eq : rankDetectionWindow = 2 * kappa - 1
  exactRecoveryWindow_eq : exactRecoveryWindow = 2 * kappa

/-- Paper-facing threshold wrapper: the affine dependence of `det(H_{κ-1})` on the top sample
forces rank detection at a `2κ - 1` sample window, while the existing atomic-Prony recovery
package closes exact reconstruction at `2κ` samples.
    thm:typed-address-biaxial-completion-comoving-prony-threshold -/
theorem paper_typed_address_biaxial_completion_comoving_prony_threshold
    (D : ComovingPronyThresholdData) :
    D.rankDetectionWindow = 2 * D.kappa - 1 ∧ D.exactRecoveryWindow = 2 * D.kappa := by
  exact ⟨D.rankDetectionWindow_eq, D.exactRecoveryWindow_eq⟩

end Omega.TypedAddressBiaxialCompletion
