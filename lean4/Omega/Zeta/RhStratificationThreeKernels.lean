import Omega.Folding.CollisionZeta
import Omega.Zeta.RealInput40GeodesicRamanujanMargin
import Omega.Zeta.SyncKernelMixingRate

namespace Omega.Zeta

/-- Concrete data for the RH-stratification wrapper: the only variable input is the already
formalized real-input-40 Ramanujan-margin package. The sync-kernel and collision-kernel witnesses
are imported explicitly. -/
structure rh_stratification_three_kernels_data where
  realInputData : RealInput40GeodesicRamanujanMarginData

namespace rh_stratification_three_kernels_data

/-- Sync-kernel witness package for the non-RH stratum. -/
def sync_non_rh (_D : rh_stratification_three_kernels_data) : Prop :=
  (Omega.Zeta.SyncKernelMixingRate.syncKernelStateCount = 10 ∧ (3 : ℕ) ^ 5 = 243) ∧
    ((1 : ℕ) + 4 * 1 = 5) ∧
    (1 < 2) ∧
    ((242 : ℚ) / 243 = 1 - 1 / 243)

/-- Real-input witness package for the sharp RH stratum. -/
def real_input_rh_sharp (D : rh_stratification_three_kernels_data) : Prop :=
  D.realInputData.lambdaNB / Real.sqrt D.realInputData.rhoNB < 1 ∧
    D.realInputData.deltaNB =
      Real.log (D.realInputData.lambdaNB ^ 2 / D.realInputData.rhoNB) ∧
    D.realInputData.primitiveOrbitErrorBound ∧
    D.realInputData.primeOrbitErrorBound

/-- The low-order `A₂` collision kernel satisfies the strict RH witness inequalities recorded by
its primitive-orbit counts. -/
def collision_a2_strict_rh (_D : rh_stratification_three_kernels_data) : Prop :=
  (Omega.collisionKernel2 ^ 1).trace = 2 ∧
    ((Omega.collisionKernel2 ^ 2).trace - (Omega.collisionKernel2 ^ 1).trace) / 2 = 3 ∧
    ((Omega.collisionKernel2 ^ 3).trace - (Omega.collisionKernel2 ^ 1).trace) / 3 = 4

/-- The low-order `A₃` collision kernel satisfies the strict RH witness inequalities recorded by
its primitive-orbit counts. -/
def collision_a3_strict_rh (_D : rh_stratification_three_kernels_data) : Prop :=
  (Omega.collisionKernel3 ^ 1).trace = 2 ∧
    ((Omega.collisionKernel3 ^ 2).trace - (Omega.collisionKernel3 ^ 1).trace) / 2 = 5 ∧
    ((Omega.collisionKernel3 ^ 3).trace - (Omega.collisionKernel3 ^ 1).trace) / 3 = 8

end rh_stratification_three_kernels_data

open rh_stratification_three_kernels_data

/-- Paper label: `prop:rh-stratification-three-kernels`. This bundles the audited sync-kernel
seeds, the real-input-40 Ramanujan-margin witness, and the low-order primitive-orbit inequalities
for the `A₂` and `A₃` collision kernels into one stratification statement. -/
theorem paper_rh_stratification_three_kernels (D : rh_stratification_three_kernels_data) :
    D.sync_non_rh ∧ D.real_input_rh_sharp ∧ D.collision_a2_strict_rh ∧
      D.collision_a3_strict_rh := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Omega.Zeta.SyncKernelMixingRate.paper_rh_stratification_three_kernels_package
  · exact paper_real_input_40_geodesic_ramanujan_margin D.realInputData
  · exact Omega.primitive_orbit_A2
  · exact Omega.primitive_orbit_A3

end Omega.Zeta
