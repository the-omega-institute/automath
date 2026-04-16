import Mathlib.Data.Rat.Defs
import Mathlib.Tactic
import Omega.Folding.BinFold

namespace Omega.GU

open Finset
open scoped BigOperators

private theorem fiber_mult_pos (i : Fin 21) :
    0 < cBinFiberMult 6 (X.ofNat 6 i) := by
  have hmin :
      cBinFiberMin 6 ≤ cBinFiberMult 6 (X.ofNat 6 i) := by
    simpa [cBinFiberMin] using
      (Finset.inf'_le (s := (@Finset.univ (X 6) (fintypeX 6)))
        (f := fun x => cBinFiberMult 6 x)
        (by simp : X.ofNat 6 i ∈ (@Finset.univ (X 6) (fintypeX 6))))
  rw [cBinFiberMin_six] at hmin
  omega

private theorem kernel_row_sum (i : Fin 21) :
    (Finset.univ : Finset (Fin 21)).sum
        (fun j =>
          (cTypeAdjCount 6 (X.ofNat 6 i) (X.ofNat 6 j) : ℚ) /
            (6 * cBinFiberMult 6 (X.ofNat 6 i))) = 1 := by
  have hi : (0 : ℚ) < 6 * cBinFiberMult 6 (X.ofNat 6 i) := by
    exact_mod_cast Nat.mul_pos (by decide : 0 < 6) (fiber_mult_pos i)
  have hrowQ :
      ((Finset.univ : Finset (Fin 21)).sum
        fun j => (cTypeAdjCount 6 (X.ofNat 6 i) (X.ofNat 6 j) : ℚ)) =
      6 * cBinFiberMult 6 (X.ofNat 6 i) := by
    exact_mod_cast cTypeAdjCount_row_sum_six i
  calc
    (Finset.univ : Finset (Fin 21)).sum
        (fun j =>
          (cTypeAdjCount 6 (X.ofNat 6 i) (X.ofNat 6 j) : ℚ) /
            (6 * cBinFiberMult 6 (X.ofNat 6 i)))
        =
        (((Finset.univ : Finset (Fin 21)).sum
          fun j => (cTypeAdjCount 6 (X.ofNat 6 i) (X.ofNat 6 j) : ℚ))) /
            (6 * cBinFiberMult 6 (X.ofNat 6 i)) := by
              simp [div_eq_mul_inv, Finset.sum_mul]
    _ = (6 * cBinFiberMult 6 (X.ofNat 6 i) : ℚ) / (6 * cBinFiberMult 6 (X.ofNat 6 i)) := by
          rw [hrowQ]
    _ = 1 := by
          exact div_self (ne_of_gt hi)

private theorem detailed_balance (i j : Fin 21) :
    ((cBinFiberMult 6 (X.ofNat 6 i) : ℚ) / 64) *
        ((cTypeAdjCount 6 (X.ofNat 6 i) (X.ofNat 6 j) : ℚ) /
          (6 * cBinFiberMult 6 (X.ofNat 6 i))) =
      ((cBinFiberMult 6 (X.ofNat 6 j) : ℚ) / 64) *
        ((cTypeAdjCount 6 (X.ofNat 6 j) (X.ofNat 6 i) : ℚ) /
          (6 * cBinFiberMult 6 (X.ofNat 6 j))) := by
  have hi : (0 : ℚ) < cBinFiberMult 6 (X.ofNat 6 i) := by
    exact_mod_cast fiber_mult_pos i
  have hj : (0 : ℚ) < cBinFiberMult 6 (X.ofNat 6 j) := by
    exact_mod_cast fiber_mult_pos j
  have hsym := cTypeAdjCount_symm_six i j
  rw [hsym]
  field_simp [ne_of_gt hi, ne_of_gt hj]

/-- `thm:terminal-foldbin6-pushforward-markov` -/
theorem paper_terminal_foldbin6_pushforward_markov :
    let π : Fin 21 → ℚ := fun i => (cBinFiberMult 6 (X.ofNat 6 i) : ℚ) / 64
    let P : Fin 21 → Fin 21 → ℚ := fun i j =>
      (cTypeAdjCount 6 (X.ofNat 6 i) (X.ofNat 6 j) : ℚ) /
        (6 * cBinFiberMult 6 (X.ofNat 6 i))
    (∀ i, (Finset.univ : Finset (Fin 21)).sum (P i) = 1) ∧
      (∀ i j, π i * P i j = π j * P j i) := by
  dsimp
  refine ⟨kernel_row_sum, detailed_balance⟩

end Omega.GU
