import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic
import Omega.DerivedConsequences.DerivedWindow6ZeroSetMultiplicativeHalfExponent
import Omega.Folding.FoldZeroWindow6DensitySharpExponent

open Filter Topology
open scoped goldenRatio

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-sixfold-zero-witness-square-root-law`. -/
theorem paper_conclusion_sixfold_zero_witness_square_root_law :
    Tendsto
      (fun n : Nat =>
        Real.log (((Omega.Folding.foldZeroFrequencyUnion (6 * n + 4)).card : Nat) : Real) /
          Real.log ((Nat.fib (6 * n + 6) : Nat) : Real))
      atTop (nhds (1 / 2 : Real)) := by
  rcases Omega.Folding.paper_fold_zero_window6_density_sharp_exponent with
    ⟨hlower, _, _, hden⟩
  rcases Omega.DerivedConsequences.paper_derived_window6_zero_set_multiplicative_half_exponent
    with ⟨habsLower, habsUpper⟩
  have hlogPhi_ne : Real.log Real.goldenRatio ≠ 0 := by
    exact ne_of_gt (Real.log_pos Real.one_lt_goldenRatio)
  have hLowerRatio :
      Tendsto
        (fun n : Nat =>
          Real.log ((Nat.fib (3 * n + 3) : Nat) : Real) /
            Real.log ((Nat.fib (6 * n + 6) : Nat) : Real))
        atTop (nhds (1 / 2 : Real)) := by
    have hquot :=
      habsLower.div hden hlogPhi_ne
    convert hquot using 1
    · ext n
      have hm : (((6 * n + 4 : Nat) : Real)) ≠ 0 := by positivity
      symm
      exact div_div_div_cancel_right₀ hm _ _
    · field_simp [hlogPhi_ne]
  have hUpperRatio :
      Tendsto
        (fun n : Nat =>
          Real.log ((((6 * n + 6).divisors.card * Nat.fib (3 * n + 3) : Nat) : Real)) /
            Real.log ((Nat.fib (6 * n + 6) : Nat) : Real))
        atTop (nhds (1 / 2 : Real)) := by
    have hquot :=
      habsUpper.div hden hlogPhi_ne
    convert hquot using 1
    · ext n
      have hm : (((6 * n + 4 : Nat) : Real)) ≠ 0 := by positivity
      symm
      exact div_div_div_cancel_right₀ hm _ _
    · field_simp [hlogPhi_ne]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hLowerRatio hUpperRatio ?_ ?_
  · intro n
    have hfibSmallPosNat : 0 < Nat.fib (3 * n + 3) :=
      Nat.fib_pos.mpr (by omega)
    have hcardPosNat :
        0 < (Omega.Folding.foldZeroFrequencyUnion (6 * n + 4)).card :=
      lt_of_lt_of_le hfibSmallPosNat (hlower n)
    have hfibSmallPos :
        0 < ((Nat.fib (3 * n + 3) : Nat) : Real) := by
      exact_mod_cast hfibSmallPosNat
    have hsmall_le_card :
        ((Nat.fib (3 * n + 3) : Nat) : Real) ≤
          (((Omega.Folding.foldZeroFrequencyUnion (6 * n + 4)).card : Nat) : Real) := by
      exact_mod_cast hlower n
    have hlog_le :
        Real.log ((Nat.fib (3 * n + 3) : Nat) : Real) ≤
          Real.log (((Omega.Folding.foldZeroFrequencyUnion (6 * n + 4)).card : Nat) : Real) :=
      Real.log_le_log hfibSmallPos hsmall_le_card
    have hfibLargeGtOneNat : 1 < Nat.fib (6 * n + 6) := by
      exact lt_of_lt_of_le (by omega : 1 < 6 * n + 6) (Nat.le_fib_self (by omega))
    have hfibLargeGtOne :
        (1 : Real) < ((Nat.fib (6 * n + 6) : Nat) : Real) := by
      exact_mod_cast hfibLargeGtOneNat
    have hdenPos :
        0 < Real.log ((Nat.fib (6 * n + 6) : Nat) : Real) :=
      Real.log_pos hfibLargeGtOne
    exact div_le_div_of_nonneg_right hlog_le (le_of_lt hdenPos)
  · intro n
    have hfibSmallPosNat : 0 < Nat.fib (3 * n + 3) :=
      Nat.fib_pos.mpr (by omega)
    have hcardPosNat :
        0 < (Omega.Folding.foldZeroFrequencyUnion (6 * n + 4)).card :=
      lt_of_lt_of_le hfibSmallPosNat (hlower n)
    have hcardPos :
        0 < (((Omega.Folding.foldZeroFrequencyUnion (6 * n + 4)).card : Nat) : Real) := by
      exact_mod_cast hcardPosNat
    have hcard_le_product :
        (((Omega.Folding.foldZeroFrequencyUnion (6 * n + 4)).card : Nat) : Real) ≤
          (((6 * n + 6).divisors.card * Nat.fib (3 * n + 3) : Nat) : Real) := by
      have hEvenFib : Even (Nat.fib (6 * n + 6)) := by
        exact even_iff_two_dvd.mpr ((Omega.fib_even_iff_three_dvd (6 * n + 6)).2 (by omega))
      have hsparse := (Omega.Folding.paper_fold_zero_density_sparse (6 * n + 4) hEvenFib).1
      have hidx : (6 * n + 4 + 2) / 2 = 3 * n + 3 := by omega
      exact_mod_cast (by simpa [hidx] using hsparse)
    have hlog_le :
        Real.log (((Omega.Folding.foldZeroFrequencyUnion (6 * n + 4)).card : Nat) : Real) ≤
          Real.log ((((6 * n + 6).divisors.card * Nat.fib (3 * n + 3) : Nat) : Real)) :=
      Real.log_le_log hcardPos hcard_le_product
    have hfibLargeGtOneNat : 1 < Nat.fib (6 * n + 6) := by
      exact lt_of_lt_of_le (by omega : 1 < 6 * n + 6) (Nat.le_fib_self (by omega))
    have hfibLargeGtOne :
        (1 : Real) < ((Nat.fib (6 * n + 6) : Nat) : Real) := by
      exact_mod_cast hfibLargeGtOneNat
    have hdenPos :
        0 < Real.log ((Nat.fib (6 * n + 6) : Nat) : Real) :=
      Real.log_pos hfibLargeGtOne
    exact div_le_div_of_nonneg_right hlog_le (le_of_lt hdenPos)

end Omega.Conclusion
