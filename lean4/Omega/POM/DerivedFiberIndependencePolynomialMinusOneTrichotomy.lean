import Omega.POM.DerivedFiberIndcomplexAlternatingWittenParity

namespace Omega.POM

/-- Wrapper identifying the `-1` specialization of the derived fiber independence polynomial with
the already formalized alternating-Witten parity package.
    cor:derived-fiber-independence-polynomial-minus-one-trichotomy -/
theorem paper_derived_fiber_independence_polynomial_minus_one_trichotomy
    (D : Omega.POM.FiberIndependenceComplexClassificationData) (L : List ℕ) (tau : ℕ)
    (E : Omega.POM.POMFiberStokesEulerBoundaryObservabilityData)
    (hBad : (∃ ℓ ∈ L, ℓ % 3 = 1) → D.badModThreeComponent)
    (hGood : (∀ ℓ ∈ L, ℓ % 3 ≠ 1) → D.allComponentsAvoidBadModThree)
    (hContractibleEuler : D.contractibleCase → E.reducedEulerCharacteristic = 0)
    (hSphereEuler : D.sphereCase → E.reducedEulerCharacteristic = (-1 : ℤ) ^ (tau - 1))
    (hTauPos : D.sphereCase → 1 ≤ tau) :
    (((L.map (fun ℓ => Nat.fib (ℓ + 2))).prod % 2 = 0) → E.zAtMinusOne = 0) ∧
      (((L.map (fun ℓ => Nat.fib (ℓ + 2))).prod % 2 = 1) → E.zAtMinusOne = (-1 : ℤ) ^ tau) := by
  exact
    paper_derived_fiber_indcomplex_alternating_witten_parity D L tau E hBad hGood
      hContractibleEuler hSphereEuler hTauPos

end Omega.POM
