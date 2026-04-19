import Mathlib.Tactic
import Omega.POM.FiberIndependenceComplexClassification
import Omega.POM.FiberParityMod3

namespace Omega.POM

private lemma exists_bad_mod_three_component
    (L : List ℕ) (h : ¬ ∀ ℓ ∈ L, ℓ % 3 ≠ 1) : ∃ ℓ ∈ L, ℓ % 3 = 1 := by
  induction L with
  | nil =>
      exfalso
      apply h
      simp
  | cons a L ih =>
      by_cases ha : a % 3 = 1
      · exact ⟨a, by simp, ha⟩
      · have hTail : ¬ ∀ ℓ ∈ L, ℓ % 3 ≠ 1 := by
          intro hAllGood
          apply h
          intro ℓ hℓ
          rcases List.mem_cons.1 hℓ with rfl | hℓ
          · exact ha
          · exact hAllGood ℓ hℓ
        rcases ih hTail with ⟨ℓ, hℓ, hBadℓ⟩
        exact ⟨ℓ, by simp [hℓ], hBadℓ⟩

/-- Paper label: `thm:pom-fiber-parity-homotopy-equivalence`.
The parity test from the Fibonacci factors detects the bad `1 mod 3` path components, and once
those component-level implications are supplied the classification package turns parity into the
contractible-versus-sphere dichotomy. -/
theorem paper_pom_fiber_parity_homotopy_equivalence
    (D : FiberIndependenceComplexClassificationData) (L : List ℕ)
    (hBad : (∃ ℓ ∈ L, ℓ % 3 = 1) → D.badModThreeComponent)
    (hGood : (∀ ℓ ∈ L, ℓ % 3 ≠ 1) → D.allComponentsAvoidBadModThree) :
    (((L.map (fun ℓ => Nat.fib (ℓ + 2))).prod % 2 = 0) → D.contractibleCase) ∧
      (((L.map (fun ℓ => Nat.fib (ℓ + 2))).prod % 2 = 1) → D.sphereCase) := by
  refine ⟨?_, ?_⟩
  · intro hEven
    have hNotAllGood : ¬ ∀ ℓ ∈ L, ℓ % 3 ≠ 1 := by
      intro hAllGood
      have hOdd : (L.map (fun ℓ => Nat.fib (ℓ + 2))).prod % 2 = 1 :=
        (paper_pom_fiber_parity_mod3 L).2 hAllGood
      omega
    rcases exists_bad_mod_three_component L hNotAllGood with ⟨ℓ, hℓ, hBadℓ⟩
    exact D.badModThreeComponentForcesContraction
      (hBad ⟨ℓ, hℓ, hBadℓ⟩) D.hasJoinDecomposition
  · intro hOdd
    have hAllGood : ∀ ℓ ∈ L, ℓ % 3 ≠ 1 := (paper_pom_fiber_parity_mod3 L).1 hOdd
    exact D.allGoodComponentsGiveSphere (hGood hAllGood) D.hasJoinDecomposition

end Omega.POM
