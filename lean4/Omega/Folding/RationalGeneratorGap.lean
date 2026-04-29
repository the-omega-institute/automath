import Mathlib.Tactic
import Omega.Folding.FiberArithmetic

namespace Omega.Folding.RationalGeneratorGap

open Finset Omega.Folding

/-- Rational generator gap: `g_rat(m) = ∑_{x ∈ X_m} (d_m(x) - 1)`.
    thm:fold-groupoid-aut0-rational-generator-gap -/
noncomputable def g_rat (m : ℕ) : ℕ :=
  ∑ x : X m, (X.fiberMultiplicity x - 1)

/-- Sum of `(d - 1)` plus `|X_m|` recovers `∑ d`.
    thm:fold-groupoid-aut0-rational-generator-gap -/
theorem g_rat_add_card (m : ℕ) :
    g_rat m + (Finset.univ : Finset (X m)).card =
      ∑ x : X m, X.fiberMultiplicity x := by
  unfold g_rat
  rw [show ((Finset.univ : Finset (X m)).card : ℕ) =
        ∑ _x : X m, (1 : ℕ) from
      (by rw [Finset.sum_const, smul_eq_mul, mul_one])]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  have hpos : 0 < X.fiberMultiplicity x := X.fiberMultiplicity_pos x
  omega

/-- `g_rat = 2^m - |X_m|` (using `fiberMultiplicity_sum_eq_pow`).
    thm:fold-groupoid-aut0-rational-generator-gap -/
theorem g_rat_eq (m : ℕ) :
    g_rat m = 2 ^ m - (Finset.univ : Finset (X m)).card := by
  have h := g_rat_add_card m
  rw [X.fiberMultiplicity_sum_eq_pow] at h
  omega

/-- Paper package: fold groupoid Aut₀ rational generator gap.
    thm:fold-groupoid-aut0-rational-generator-gap -/
theorem paper_fold_groupoid_aut0_rational_generator_gap (m : ℕ) :
    g_rat m = 2 ^ m - (Finset.univ : Finset (X m)).card :=
  g_rat_eq m

/-- Cup-length and rational category witnesses inherit the rational generator gap formula.
    thm:fold-groupoid-aut0-rational-generator-gap -/
theorem paper_fold_groupoid_aut0_rational_generator_gap_cuplength_cat0
    (m cup cat : ℕ) (hcup : cup = g_rat m) (hcat : cat = g_rat m) :
    cup = 2 ^ m - (Finset.univ : Finset (X m)).card ∧
      cat = 2 ^ m - (Finset.univ : Finset (X m)).card := by
  constructor
  · rw [hcup]
    exact paper_fold_groupoid_aut0_rational_generator_gap m
  · rw [hcat]
    exact paper_fold_groupoid_aut0_rational_generator_gap m

end Omega.Folding.RationalGeneratorGap
