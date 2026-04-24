import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
import Omega.Folding.Entropy
import Omega.Folding.MaxFiberHigh

namespace Omega.Zeta

/-- Concrete Stinespring lower-bound hypothesis for the fold model at resolution `m`. -/
def dephys_fold_stinespring_sqrt_law_stinespring_bound (m d : ℕ) : Prop :=
  (Omega.X.maxFiberMultiplicity m : ℝ) ≤ (d : ℝ) ^ 2

private lemma dephys_fold_stinespring_sqrt_law_fib_lower (k : ℕ) :
    Real.goldenRatio ^ k / 2 ≤ (Nat.fib (k + 2) : ℝ) := by
  have hFib := Omega.Entropy.fib_growth_sandwich (k + 2)
  have hphi_sq_gt_sqrt5 : Real.sqrt 5 < Real.goldenRatio ^ 2 := by
    rw [Real.goldenRatio_sq]
    exact Omega.Entropy.phi_add_one_gt_sqrt5
  have hfactor_gt_one : 1 < Real.goldenRatio ^ 2 / Real.sqrt 5 := by
    have hsqrt5_pos : 0 < Real.sqrt 5 := by positivity
    exact (one_lt_div hsqrt5_pos).2 hphi_sq_gt_sqrt5
  have hphi_factor :
      Real.goldenRatio ^ k < Real.goldenRatio ^ (k + 2) / Real.sqrt 5 := by
    have hk_pos : 0 < Real.goldenRatio ^ k := by positivity
    calc
      Real.goldenRatio ^ k = Real.goldenRatio ^ k * 1 := by ring
      _ < Real.goldenRatio ^ k * (Real.goldenRatio ^ 2 / Real.sqrt 5) := by
        exact mul_lt_mul_of_pos_left hfactor_gt_one hk_pos
      _ = Real.goldenRatio ^ (k + 2) / Real.sqrt 5 := by
        field_simp [show (Real.sqrt 5 : ℝ) ≠ 0 by positivity]
        rw [pow_add]
        ring
  have hpow_ge_one : 1 ≤ Real.goldenRatio ^ k := by
    simpa using
      (one_le_pow₀ (n := k) (a := Real.goldenRatio) (le_of_lt Real.one_lt_goldenRatio))
  have hhalf :
      Real.goldenRatio ^ k / 2 ≤ Real.goldenRatio ^ k - 1 / 2 := by
    linarith
  have hmid : Real.goldenRatio ^ k - 1 / 2 < (Nat.fib (k + 2) : ℝ) := by
    linarith [hphi_factor, hFib.1]
  exact le_of_lt (lt_of_le_of_lt hhalf hmid)

/-- Paper label: `cor:dephys-fold-stinespring-sqrt-law`.
For audited even fold windows `m = 2k` with `1 ≤ k ≤ 5`, any concrete Stinespring realization
whose ancillary dimension is `d` and whose environment obeys the lower-bound certificate
`D_m ≤ d^2` satisfies the square-root index law together with the explicit growth lower bound
`sqrt(φ^k / 2) ≤ d`. -/
theorem paper_dephys_fold_stinespring_sqrt_law
    (k d : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 5)
    (hStine : dephys_fold_stinespring_sqrt_law_stinespring_bound (2 * k) d) :
    (∃ x : Omega.X (2 * k), Omega.X.fiberMultiplicity x = Omega.X.maxFiberMultiplicity (2 * k)) ∧
      0 < Omega.X.maxFiberMultiplicity (2 * k) ∧
      Real.sqrt (Omega.X.maxFiberMultiplicity (2 * k)) ≤ d ∧
      Real.sqrt (Real.goldenRatio ^ k / 2) ≤ d := by
  have hach := Omega.X.maxFiberMultiplicity_achieved (2 * k)
  have hpos := Omega.X.maxFiberMultiplicity_pos (2 * k)
  have hsqrt_bound : Real.sqrt (Omega.X.maxFiberMultiplicity (2 * k)) ≤ d := by
    have := Real.sqrt_le_sqrt hStine
    simpa [sq, Real.sqrt_sq_eq_abs, abs_of_nonneg (show 0 ≤ (d : ℝ) by positivity)] using this
  have hclosed : Omega.X.maxFiberMultiplicity (2 * k) = Nat.fib (k + 2) :=
    Omega.X.maxFiberMultiplicity_even_ext k hk hk'
  have hgrowth_sq :
      Real.goldenRatio ^ k / 2 ≤ (Omega.X.maxFiberMultiplicity (2 * k) : ℝ) := by
    simpa [hclosed] using dephys_fold_stinespring_sqrt_law_fib_lower k
  have hgrowth :
      Real.sqrt (Real.goldenRatio ^ k / 2) ≤ d := by
    have htrans : Real.goldenRatio ^ k / 2 ≤ (d : ℝ) ^ 2 := le_trans hgrowth_sq hStine
    have := Real.sqrt_le_sqrt htrans
    simpa [Real.sqrt_sq_eq_abs, abs_of_nonneg (show 0 ≤ (d : ℝ) by positivity)] using this
  exact ⟨hach, hpos, hsqrt_bound, hgrowth⟩

end Omega.Zeta
