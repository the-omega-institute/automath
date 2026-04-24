import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- A uniform `N^(1 - δ)` saving bound for a concrete character sum. -/
def spectralGapSavingBound (N : ℕ) (δ C : ℝ) (S : ℂ) : Prop :=
  ‖S‖ ≤ C * (N : ℝ) ^ (1 - δ)

/-- The multiplicative channel bound in the double large-sieve input. -/
def multiplicativeLargeSieveSaving (N : ℕ) (δ C : ℝ) (S : ℂ) : Prop :=
  spectralGapSavingBound N δ C S

/-- The additive channel bound in the double large-sieve input. -/
def additiveLargeSieveSaving (N : ℕ) (δ C : ℝ) (S : ℂ) : Prop :=
  spectralGapSavingBound N δ C S

lemma nat_mul_rpow_neg_eq_rpow_sub (N : ℕ) (hN : 0 < (N : ℝ)) (δ : ℝ) :
    (N : ℝ) * (N : ℝ) ^ (-δ) = (N : ℝ) ^ (1 - δ) := by
  calc
    (N : ℝ) * (N : ℝ) ^ (-δ) = (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (-δ) := by
      rw [Real.rpow_one]
    _ = (N : ℝ) ^ ((1 : ℝ) + (-δ)) := by
      rw [← Real.rpow_add hN]
    _ = (N : ℝ) ^ (1 - δ) := by ring_nf

/-- Paper label: `prop:conclusion74-double-large-sieve-input`. -/
theorem paper_conclusion74_double_large_sieve_input
    (N : ℕ) (_hN : 2 ≤ N)
    (δ₁ δ₂ C₁ C₂ : ℝ)
    (hδ₁ : 0 < δ₁)
    (hδ₂ : 0 < δ₂)
    (multiplicativeSum additiveSum : ℂ)
    (hmulGap : ‖multiplicativeSum‖ ≤ C₁ * (N : ℝ) * (N : ℝ) ^ (-δ₁))
    (haddGap : ‖additiveSum‖ ≤ C₂ * (N : ℝ) * (N : ℝ) ^ (-δ₂)) :
    multiplicativeLargeSieveSaving N δ₁ C₁ multiplicativeSum ∧
      additiveLargeSieveSaving N δ₂ C₂ additiveSum := by
  let _ := hδ₁
  let _ := hδ₂
  have hNreal : 0 < (N : ℝ) := by
    have hNnat : 0 < N := lt_of_lt_of_le (by norm_num : 0 < 2) _hN
    exact_mod_cast hNnat
  constructor
  · dsimp [multiplicativeLargeSieveSaving, spectralGapSavingBound]
    calc
      ‖multiplicativeSum‖ ≤ C₁ * (N : ℝ) * (N : ℝ) ^ (-δ₁) := hmulGap
      _ = C₁ * (N : ℝ) ^ (1 - δ₁) := by
        rw [mul_assoc, nat_mul_rpow_neg_eq_rpow_sub N hNreal δ₁]
  · dsimp [additiveLargeSieveSaving, spectralGapSavingBound]
    calc
      ‖additiveSum‖ ≤ C₂ * (N : ℝ) * (N : ℝ) ^ (-δ₂) := haddGap
      _ = C₂ * (N : ℝ) ^ (1 - δ₂) := by
        rw [mul_assoc, nat_mul_rpow_neg_eq_rpow_sub N hNreal δ₂]

end

end Omega.Zeta
