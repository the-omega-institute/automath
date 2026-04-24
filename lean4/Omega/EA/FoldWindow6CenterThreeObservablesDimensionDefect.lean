import Mathlib.Tactic
import Omega.EA.Wedderburn

namespace Omega.EA

/-- The four sector bounds used by the center/three-observable resolution at window `6`. -/
def foldWindow6CenterThreeObservableSectorBound : Fin 4 → ℕ
  | 0 => 2
  | 1 => 3
  | 2 => 3
  | _ => 4

/-- The resolved dimension obtained by summing the four sector bounds. -/
def foldWindow6CenterThreeObservablesResolvedDimension : ℕ :=
  ∑ i : Fin 4, foldWindow6CenterThreeObservableSectorBound i

/-- The residual center-dimension defect after keeping only the four audited sectors. -/
noncomputable def foldWindow6CenterThreeObservablesDimensionDefect : ℕ :=
  momentSum 0 6 - foldWindow6CenterThreeObservablesResolvedDimension

private lemma foldWindow6CenterThreeObservables_saturation
    {a b c d : ℕ} (ha : a ≤ 2) (hb : b ≤ 3) (hc : c ≤ 3) (hd : d ≤ 4) :
    a + b + c + d = 12 ↔ a = 2 ∧ b = 3 ∧ c = 3 ∧ d = 4 := by
  constructor
  · intro hsum
    omega
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    omega

/-- The window-`6` center has dimension `21`, the four audited three-observable sectors contribute
at most `2 + 3 + 3 + 4 = 12`, so the remaining defect is `9`. Equality in the sector bound occurs
exactly when all four cardinality bounds are saturated.
    thm:fold-window6-center-three-observables-dimension-defect -/
theorem paper_fold_window6_center_three_observables_dimension_defect :
    0 < cFiberHist 6 2 ∧
      1 < cFiberHist 6 3 ∧
      0 < cFiberHist 6 4 ∧
      foldWindow6CenterThreeObservablesResolvedDimension = 12 ∧
      momentSum 0 6 = 21 ∧
      foldWindow6CenterThreeObservablesDimensionDefect = 9 ∧
      ∀ a b c d : ℕ, a ≤ 2 → b ≤ 3 → c ≤ 3 → d ≤ 4 →
        (a + b + c + d = 12 ↔ a = 2 ∧ b = 3 ∧ c = 3 ∧ d = 4) := by
  rcases fiber_histogram_m6 with ⟨_, h2, h3, h4, _⟩
  have hdim : momentSum 0 6 = 21 := paper_sector_dimension_sum_m6.2.1
  refine ⟨?_, ?_, ?_, ?_, hdim, ?_, ?_⟩
  · omega
  · omega
  · omega
  · native_decide
  · rw [foldWindow6CenterThreeObservablesDimensionDefect, hdim]
    native_decide
  · intro a b c d ha hb hc hd
    exact foldWindow6CenterThreeObservables_saturation ha hb hc hd

end Omega.EA
