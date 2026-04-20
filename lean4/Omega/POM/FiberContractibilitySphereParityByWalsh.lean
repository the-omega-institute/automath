import Mathlib.Tactic
import Omega.POM.FiberIndependenceComplexClassification
import Omega.POM.FiberStokesEulerBoundaryObservability

namespace Omega.POM

/-- Contractible fibers are exactly the vanishing-Walsh branch, while sphere fibers recover the
sphere parity from the parity-corrected Walsh readout. -/
theorem paper_pom_fiber_contractibility_sphere_parity_by_walsh
    (D : FiberIndependenceComplexClassificationData) (E : POMFiberStokesEulerBoundaryObservabilityData)
    (tau : ℕ) (hContractibleEuler : D.contractibleCase → E.reducedEulerCharacteristic = 0)
    (hSphereEuler : D.sphereCase → E.reducedEulerCharacteristic = (-1 : ℤ) ^ (tau - 1)) :
    (D.contractibleCase → E.walshReadout = 0) ∧
      (D.sphereCase → (-1 : ℤ) ^ (tau - 1) = -((-1 : ℤ) ^ E.parity) * E.walshReadout) := by
  have hObservable := paper_pom_fiber_stokes_euler_characteristic_boundary_observable E
  dsimp [POMFiberStokesEulerBoundaryObservabilityData.eulerCharacteristicBoundaryObservable] at hObservable
  refine ⟨?_, ?_⟩
  · intro hContractible
    have hEuler : E.reducedEulerCharacteristic = 0 := hContractibleEuler hContractible
    rw [hEuler, mul_zero] at hObservable
    linarith
  · intro hSphere
    have hEuler : E.reducedEulerCharacteristic = (-1 : ℤ) ^ (tau - 1) := hSphereEuler hSphere
    have hParitySq : ((-1 : ℤ) ^ E.parity) * ((-1 : ℤ) ^ E.parity) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]
      norm_num
    rw [hEuler] at hObservable
    calc
      (-1 : ℤ) ^ (tau - 1) =
          (((-1 : ℤ) ^ E.parity) * ((-1 : ℤ) ^ E.parity)) * ((-1 : ℤ) ^ (tau - 1)) := by
            rw [hParitySq, one_mul]
      _ = ((-1 : ℤ) ^ E.parity) * (((-1 : ℤ) ^ E.parity) * ((-1 : ℤ) ^ (tau - 1))) := by ring
      _ = ((-1 : ℤ) ^ E.parity) * (-E.walshReadout) := by rw [hObservable]
      _ = -((-1 : ℤ) ^ E.parity) * E.walshReadout := by ring

end Omega.POM
