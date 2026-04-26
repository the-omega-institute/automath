import Mathlib.Tactic
import Omega.POM.FiberParityHomotopyEquivalence
import Omega.POM.FiberStokesEulerBoundaryObservability

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part62dg-fiber-reduced-euler-witten-parity`. -/
theorem paper_xi_time_part62dg_fiber_reduced_euler_witten_parity
    (D : Omega.POM.FiberIndependenceComplexClassificationData) (L : List ℕ) (tau : ℕ)
    (E : Omega.POM.POMFiberStokesEulerBoundaryObservabilityData)
    (hBad : (∃ ℓ ∈ L, ℓ % 3 = 1) → D.badModThreeComponent)
    (hGood : (∀ ℓ ∈ L, ℓ % 3 ≠ 1) → D.allComponentsAvoidBadModThree)
    (hContractibleEuler : D.contractibleCase → E.reducedEulerCharacteristic = 0)
    (hSphereEuler : D.sphereCase → E.reducedEulerCharacteristic = (-1 : ℤ) ^ (tau - 1)) :
    (((L.map (fun ℓ => Nat.fib (ℓ + 2))).prod % 2 = 0) →
        E.reducedEulerCharacteristic = 0) ∧
      (((L.map (fun ℓ => Nat.fib (ℓ + 2))).prod % 2 = 1) →
        E.reducedEulerCharacteristic = (-1 : ℤ) ^ (tau - 1)) := by
  rcases Omega.POM.paper_pom_fiber_parity_homotopy_equivalence D L hBad hGood with
    ⟨hEven, hOdd⟩
  exact ⟨fun hParity => hContractibleEuler (hEven hParity),
    fun hParity => hSphereEuler (hOdd hParity)⟩

end Omega.Zeta
