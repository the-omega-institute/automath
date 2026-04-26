import Mathlib.Tactic
import Omega.POM.FiberParityMod3
import Omega.POM.ToggleScanSignGeneralFiber

namespace Omega.POM

/-- Paper label: `cor:pom-toggle-contractible-parity-rigidity`.
The contractible parity branch forces a bad `1 mod 3` component, hence a nonempty exceptional
set; once this set is nonempty, the general-fiber sign package rigidifies the sign into the
`|A| ≥ 2` branch or the unique exceptional-path branch. -/
theorem paper_pom_toggle_contractible_parity_rigidity (lengths : List ℕ) :
    let A := toggleScanExceptionalLengths lengths
    (((lengths.map (fun ℓ => Nat.fib (ℓ + 2))).prod % 2 = 0) →
      A ≠ [] ∧
        ((2 ≤ A.length → toggleScanGeneralFiberSign lengths = 1) ∧
          (∀ ℓ : ℕ, A = [ℓ] →
            toggleScanGeneralFiberSign lengths = toggleScanSinglePathSign ℓ ∧
              (ℓ % 6 = 1 ∨ ℓ % 6 = 4)))) := by
  dsimp
  intro hEven
  have hSplit := paper_pom_toggle_scan_sign_general_fiber lengths
  refine ⟨?_, hSplit.1, ?_⟩
  · intro hA
    have hAllGood : ∀ ℓ ∈ lengths, ℓ % 3 ≠ 1 := by
      simpa [toggleScanExceptionalLengths] using hA
    have hOdd : (lengths.map (fun ℓ => Nat.fib (ℓ + 2))).prod % 2 = 1 :=
      (paper_pom_fiber_parity_mod3 lengths).2 hAllGood
    omega
  · intro ℓ hA
    refine ⟨hSplit.2.1 ℓ hA, ?_⟩
    have hmem : ℓ ∈ toggleScanExceptionalLengths lengths := by simpa [hA]
    have hmod3 : ℓ % 3 = 1 := by
      have hmem' : ℓ ∈ lengths ∧ ℓ % 3 = 1 := by
        simpa [toggleScanExceptionalLengths] using hmem
      exact hmem'.2
    omega

end Omega.POM
