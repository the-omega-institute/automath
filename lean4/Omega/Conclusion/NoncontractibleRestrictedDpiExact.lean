import Mathlib.Tactic
import Omega.Conclusion.NoncontractibleLossMod6Explicit
import Omega.POM.FiberParityHomotopyEquivalence

namespace Omega.Conclusion

/-- Concrete wrapper for the restricted noncontractible DPI loss and the parity-detected
contractible/spherical dichotomy on the same fiber package. -/
def conclusion_noncontractible_restricted_dpi_exact_statement
    (m : ℕ) (D : Omega.POM.FiberIndependenceComplexClassificationData) (L : List ℕ) : Prop :=
  noncontractibleLoss m = Real.log (noncontractibleFiberCount m) ∧
    ((((L.map (fun ℓ => Nat.fib (ℓ + 2))).prod % 2 = 0) → D.contractibleCase) ∧
      (((L.map (fun ℓ => Nat.fib (ℓ + 2))).prod % 2 = 1) → D.sphereCase))

/-- Paper label: `thm:conclusion-noncontractible-restricted-dpi-exact`.
The restricted noncontractible DPI loss is the logarithm of the restricted maximal fiber count,
and the noncontractible locus is detected by the parity package governing contractible versus
spherical fibers. -/
theorem paper_conclusion_noncontractible_restricted_dpi_exact
    (m : ℕ) (D : Omega.POM.FiberIndependenceComplexClassificationData) (L : List ℕ)
    (hBad : (∃ ℓ ∈ L, ℓ % 3 = 1) → D.badModThreeComponent)
    (hGood : (∀ ℓ ∈ L, ℓ % 3 ≠ 1) → D.allComponentsAvoidBadModThree) :
    conclusion_noncontractible_restricted_dpi_exact_statement m D L := by
  refine ⟨rfl, ?_⟩
  exact Omega.POM.paper_pom_fiber_parity_homotopy_equivalence D L hBad hGood

end Omega.Conclusion
