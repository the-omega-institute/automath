import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Omega.Conclusion.CapacityRamanujanPlateauLaw
import Omega.Zeta.LayeredPrimesliceLocalAlphabetFibermax
import Omega.Zeta.XiLayeredPrimesliceInventoryPrimeIndexFormula

namespace Omega.Conclusion

open scoped BigOperators
open Omega.Conclusion.CapacityRamanujanPlateauLaw

/-- The fiber-size function attached to a layer map `π`. -/
noncomputable def conclusion_primeslice_minimal_alphabet_ramanujan_plateau_fiberCard
    {X Y : Type*} (π : X → Y) (y : Y) : ℕ :=
  Nat.card (Omega.Zeta.LayerFiber π y)

/-- Paper label: `thm:conclusion-primeslice-minimal-alphabet-ramanujan-plateau`. If every layer
has maximal fiber size exactly `B`, then the Ramanujan/capacity plateau occurs at height `B`, the
minimal local prime-slice alphabet on every layer has size `B`, the maximal prime required by the
uniform inventory is the top-layer endpoint prime, and the total inventory is `k * B`. -/
theorem paper_conclusion_primeslice_minimal_alphabet_ramanujan_plateau
    {X Y : Type*} [Fintype X] [Fintype Y]
    (k B : ℕ) (hB : 1 ≤ B)
    (π : Fin k → X → Y)
    (hmax : ∀ j y,
      conclusion_primeslice_minimal_alphabet_ramanujan_plateau_fiberCard (π j) y ≤ B)
    (hwit : ∀ j, ∃ y,
      conclusion_primeslice_minimal_alphabet_ramanujan_plateau_fiberCard (π j) y = B) :
    (∀ j : Fin k,
      0 <
          deltaCapacity
            (conclusion_primeslice_minimal_alphabet_ramanujan_plateau_fiberCard (π j)) B ∧
        deltaCapacity
            (conclusion_primeslice_minimal_alphabet_ramanujan_plateau_fiberCard (π j)) (B + 1) = 0 ∧
        (∃ q : X → Fin B, Omega.Zeta.FiberwiseInjective (π j) q) ∧
        ∀ A : ℕ,
          (∃ q : X → Fin A, Omega.Zeta.FiberwiseInjective (π j) q) ↔ B ≤ A) ∧
      Omega.Folding.layeredPrime (k - 1) (B - 1) =
        Omega.Folding.nthPrime (2 ^ (k - 1) * (2 * B - 1)) ∧
      (∑ _j : Fin k, B) = k * B := by
  have hlayer :
      ∀ j : Fin k,
        0 <
            deltaCapacity
              (conclusion_primeslice_minimal_alphabet_ramanujan_plateau_fiberCard (π j)) B ∧
          deltaCapacity
              (conclusion_primeslice_minimal_alphabet_ramanujan_plateau_fiberCard (π j)) (B + 1) =
            0 ∧
          (∃ q : X → Fin B, Omega.Zeta.FiberwiseInjective (π j) q) ∧
          ∀ A : ℕ,
            (∃ q : X → Fin A, Omega.Zeta.FiberwiseInjective (π j) q) ↔ B ≤ A := by
    intro j
    let d : Y → ℕ := conclusion_primeslice_minimal_alphabet_ramanujan_plateau_fiberCard (π j)
    have hseedsB := paper_conclusion_capacity_ramanujan_plateau_law_seeds d B hB
    have hseedsSucc := paper_conclusion_capacity_ramanujan_plateau_law_seeds d (B + 1)
      (Nat.succ_le_succ (Nat.zero_le B))
    have hposB : 0 < deltaCapacity d B := by
      rcases hwit j with ⟨y, hy⟩
      exact (hseedsB.2.1).2 ⟨y, by simpa [d] using hy.ge⟩
    have hzeroSucc : deltaCapacity d (B + 1) = 0 := by
      exact (hseedsSucc.2.2).2 (by
        intro y
        have hy : d y ≤ B := hmax j y
        omega)
    have hlocalB :
        (∃ q : X → Fin B, Omega.Zeta.FiberwiseInjective (π j) q) := by
      exact
        (Omega.Zeta.paper_xi_layered_primeslice_local_alphabet_fibermax
          (Λ := Fin B) (π := π j) (B := B) (hmax j) (hwit j)).2 (by simp)
    have hlocalA :
        ∀ A : ℕ, (∃ q : X → Fin A, Omega.Zeta.FiberwiseInjective (π j) q) ↔ B ≤ A := by
      intro A
      simpa using
        (Omega.Zeta.paper_xi_layered_primeslice_local_alphabet_fibermax
          (Λ := Fin A) (π := π j) (B := B) (hmax j) (hwit j))
    exact ⟨hposB, hzeroSucc, hlocalB, hlocalA⟩
  have hprimeTop :
      Omega.Folding.layeredPrime (k - 1) (B - 1) =
        Omega.Folding.nthPrime (2 ^ (k - 1) * (2 * B - 1)) := by
    have hodd : 2 * (B - 1) + 1 = 2 * B - 1 := by
      omega
    have hindex : 2 ^ (k - 1) * (2 * (B - 1) + 1) = 2 ^ (k - 1) * (2 * B - 1) := by
      rw [hodd]
    rw [Omega.Folding.layeredPrime, Omega.Folding.primeSliceIndex, hindex]
  refine ⟨hlayer, hprimeTop, ?_⟩
  simp

end Omega.Conclusion
