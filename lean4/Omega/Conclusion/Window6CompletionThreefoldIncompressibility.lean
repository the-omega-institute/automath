import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic
import Omega.GU.Window6AbelianizedParityChargeRootCartanSplitting
import Omega.GU.Window6B3C3UniqueQuarticDetector
import Omega.GU.Window6DyadicBudget
import Omega.GU.Window6SyzygyGramSpectrumDiscriminant

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-window6-completion-threefold-incompressibility`. The visible
quartic detector fixes the closure at fourth order, the parity/Cartan block and syzygy
discriminant witness the `2/11` prime split, and the hidden cubical type together with the dyadic
budget force the minimal hidden size `43`. -/
theorem paper_conclusion_window6_completion_threefold_incompressibility :
    (∀ q : Omega.GU.QuarticInvariant,
      (Omega.GU.b3QuarticError q = 0 ∧ Omega.GU.c3QuarticError q = 0) ↔ q.2 = 0) ∧
      Fintype.card Omega.GU.Window6BoundaryParityBlock = 3 ∧
      Omega.GU.window6SyzygyLatticeDiscriminant = 11 ^ (3 : ℕ) ∧
      (∀ V : Fin 21,
        let η := if V.1 ≤ 8 then (4 : ℕ) else if V.1 ≤ 12 then 3 else 2
        (η = 4 ↔ V.1 ≤ 8) ∧ (η = 3 ↔ 9 ≤ V.1 ∧ V.1 ≤ 12) ∧ (η = 2 ↔ 13 ≤ V.1)) ∧
      2 ^ 6 - Nat.fib 8 = 43 ∧
      Nat.fib 8 + 43 = 2 ^ 6 := by
  rcases Omega.GU.paper_window6_abelianized_parity_charge_root_cartan_splitting with
    ⟨_, _, _, _, _, _, _, hBoundaryBlock, _, _, _⟩
  rcases Omega.GU.paper_window6_syzygy_gram_spectrum_discriminant with ⟨_, _, _, hDisc⟩
  rcases Omega.GU.Window6DyadicBudget.paper_gut_window6_dyadic_budget_three_stage with
    ⟨_, _, _, _, _, hHidden, _, _, hBudget⟩
  refine ⟨?_, hBoundaryBlock, hDisc, ?_, hHidden, hBudget⟩
  · intro q
    exact Omega.GU.paper_window6_b3c3_unique_quartic_detector q
  · intro V
    dsimp
    by_cases h8 : V.1 ≤ 8
    · have hnot9 : ¬ 9 ≤ V.1 := by omega
      have hnot13 : ¬ 13 ≤ V.1 := by omega
      simp [h8, hnot9, hnot13]
    · by_cases h12 : V.1 ≤ 12
      · have h9 : 9 ≤ V.1 := by omega
        have hnot13 : ¬ 13 ≤ V.1 := by omega
        simp [h8, h12, h9, hnot13]
      · have h13 : 13 ≤ V.1 := by omega
        simp [h8, h12, h13]

end Omega.Conclusion
