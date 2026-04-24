import Mathlib.Tactic
import Omega.POM.FiberParityHomotopyEquivalence

namespace Omega.Folding

/-- The parity of the fold-fiber multiplicity `d_m(x) = ∏ᵢ F_{ℓᵢ+2}` attached to the path-length
list `L`. -/
def killo_fold_fiber_homotopy_parity_equivalence_multiplicity_parity (L : List ℕ) : ℕ :=
  (L.map (fun ℓ => Nat.fib (ℓ + 2))).prod % 2

/-- Paper-facing formulation of the fold-fiber homotopy/parity equivalence. The forward
implications come from the existing POM parity-to-homotopy theorem, while the converse
implications are supplied by the path-component mod-`3` classification hypotheses. -/
def killo_fold_fiber_homotopy_parity_equivalence_statement
    (D : Omega.POM.FiberIndependenceComplexClassificationData) (L : List ℕ) : Prop :=
  ((∃ ℓ ∈ L, ℓ % 3 = 1) → D.badModThreeComponent) →
    ((∀ ℓ ∈ L, ℓ % 3 ≠ 1) → D.allComponentsAvoidBadModThree) →
    (D.contractibleCase → ∃ ℓ ∈ L, ℓ % 3 = 1) →
    (D.sphereCase → ∀ ℓ ∈ L, ℓ % 3 ≠ 1) →
      (D.contractibleCase ↔
          killo_fold_fiber_homotopy_parity_equivalence_multiplicity_parity L = 0) ∧
        (D.sphereCase ↔
          killo_fold_fiber_homotopy_parity_equivalence_multiplicity_parity L = 1)

/-- Paper label: `thm:killo-fold-fiber-homotopy-parity-equivalence`. -/
theorem paper_killo_fold_fiber_homotopy_parity_equivalence
    (D : Omega.POM.FiberIndependenceComplexClassificationData) (L : List ℕ) :
    killo_fold_fiber_homotopy_parity_equivalence_statement D L := by
  intro hBad hGood hContractible hSphere
  rcases Omega.POM.paper_pom_fiber_parity_homotopy_equivalence D L hBad hGood with
    ⟨hEven, hOdd⟩
  refine ⟨?_, ?_⟩
  · constructor
    · intro hContractibleCase
      have hParityNeOne :
          killo_fold_fiber_homotopy_parity_equivalence_multiplicity_parity L ≠ 1 := by
        intro hParityOne
        have hAllGood : ∀ ℓ ∈ L, ℓ % 3 ≠ 1 :=
          (Omega.POM.paper_pom_fiber_parity_mod3 L).1 hParityOne
        rcases hContractible hContractibleCase with ⟨ℓ, hℓ, hmod⟩
        exact (hAllGood ℓ hℓ) hmod
      rcases Nat.mod_two_eq_zero_or_one
          ((L.map (fun ℓ => Nat.fib (ℓ + 2))).prod) with hParityZero | hParityOne
      · exact hParityZero
      · exact False.elim (hParityNeOne hParityOne)
    · exact hEven
  · constructor
    · intro hSphereCase
      exact (Omega.POM.paper_pom_fiber_parity_mod3 L).2 (hSphere hSphereCase)
    · exact hOdd

end Omega.Folding
