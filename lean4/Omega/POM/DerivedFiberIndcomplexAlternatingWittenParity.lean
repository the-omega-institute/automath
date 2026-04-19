import Mathlib.Tactic
import Omega.POM.FiberParityHomotopyEquivalence
import Omega.POM.FiberStokesEulerBoundaryObservability

namespace Omega.POM

private lemma neg_pow_pred_eq_pow (tau : ℕ) (htau : 1 ≤ tau) :
    -((-1 : ℤ) ^ (tau - 1)) = (-1 : ℤ) ^ tau := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le htau
  have hsub : 1 + n - 1 = n := by omega
  have hpow : (-1 : ℤ) ^ (1 + n) = -((-1 : ℤ) ^ n) := by
    rw [show 1 + n = n + 1 by omega, pow_succ]
    ring
  simpa [hsub] using hpow.symm

/-- The alternating Witten count of a fiber independence complex is determined by the parity split:
the even branch is contractible and contributes `0`, while the odd branch is a sphere and
contributes the sphere sign `(-1)^τ`. -/
theorem paper_derived_fiber_indcomplex_alternating_witten_parity
    (D : FiberIndependenceComplexClassificationData) (L : List ℕ)
    (tau : ℕ) (E : POMFiberStokesEulerBoundaryObservabilityData)
    (hBad : (∃ ℓ ∈ L, ℓ % 3 = 1) → D.badModThreeComponent)
    (hGood : (∀ ℓ ∈ L, ℓ % 3 ≠ 1) → D.allComponentsAvoidBadModThree)
    (hContractibleEuler : D.contractibleCase → E.reducedEulerCharacteristic = 0)
    (hSphereEuler : D.sphereCase → E.reducedEulerCharacteristic = (-1 : ℤ) ^ (tau - 1))
    (hTauPos : D.sphereCase → 1 ≤ tau) :
    (((L.map (fun ℓ => Nat.fib (ℓ + 2))).prod % 2 = 0) → E.zAtMinusOne = 0) ∧
      (((L.map (fun ℓ => Nat.fib (ℓ + 2))).prod % 2 = 1) → E.zAtMinusOne = (-1 : ℤ) ^ tau) := by
  rcases paper_pom_fiber_parity_homotopy_equivalence D L hBad hGood with ⟨hEven, hOdd⟩
  refine ⟨?_, ?_⟩
  · intro hParity
    have hEuler : E.reducedEulerCharacteristic = 0 := hContractibleEuler (hEven hParity)
    rw [E.hEulerFromWitten] at hEuler
    simpa using hEuler
  · intro hParity
    have hSphere : D.sphereCase := hOdd hParity
    have hEuler : E.reducedEulerCharacteristic = (-1 : ℤ) ^ (tau - 1) := hSphereEuler hSphere
    have htau : 1 ≤ tau := hTauPos hSphere
    rw [E.hEulerFromWitten] at hEuler
    have hWitten : E.zAtMinusOne = -((-1 : ℤ) ^ (tau - 1)) := by
      linarith
    rw [neg_pow_pred_eq_pow tau htau] at hWitten
    exact hWitten

end Omega.POM
