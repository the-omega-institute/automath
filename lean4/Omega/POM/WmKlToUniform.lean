import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.Folding.MomentRecurrence
import Omega.POM.BeckChevalleyAmgmDefectIdentity

namespace Omega.POM

open scoped BigOperators

noncomputable section

/-- The fold pushforward of the microstate-uniform law. -/
def pom_wm_kl_to_uniform_pushforward (m : ℕ) : Omega.X m → ℝ :=
  fun x => Omega.X.fiberMultiplicity x / (2 ^ m : ℕ)

/-- The uniform law on the stable syntax space `X_m`. -/
def pom_wm_kl_to_uniform_uniform (m : ℕ) : Omega.X m → ℝ :=
  fun _ => (1 : ℝ) / Fintype.card (Omega.X m)

/-- Paper label: `prop:pom-wm-kl-to-uniform`.
The fold pushforward `w_m(x) = d_m(x) / 2^m` is at KL distance at most
`log (D_m / \bar d_m) = log (D_m F_{m+2} / 2^m)` from the uniform law on `X_m`. -/
theorem paper_pom_wm_kl_to_uniform (m : ℕ) :
    klDiv (pom_wm_kl_to_uniform_pushforward m) (pom_wm_kl_to_uniform_uniform m) ≤
      Real.log
        ((Omega.X.maxFiberMultiplicity m : ℝ) * Nat.fib (m + 2) / (2 : ℝ) ^ m) := by
  let w := pom_wm_kl_to_uniform_pushforward m
  let u := pom_wm_kl_to_uniform_uniform m
  let n : ℝ := Fintype.card (Omega.X m)
  let r : ℝ := (Omega.X.maxFiberMultiplicity m : ℝ) * n / (2 : ℝ) ^ m
  have hcard_nat : 0 < Fintype.card (Omega.X m) := by
    rw [Omega.X.card_eq_fib]
    exact Nat.fib_pos.mpr (by omega)
  have hn_pos : 0 < n := by
    simpa [n] using (show (0 : ℝ) < (Fintype.card (Omega.X m) : ℝ) by exact_mod_cast hcard_nat)
  have hn_ne : n ≠ 0 := ne_of_gt hn_pos
  have hpow_pos : 0 < (2 : ℝ) ^ m := by positivity
  have hpow_ne : (2 : ℝ) ^ m ≠ 0 := ne_of_gt hpow_pos
  have hr_pos : 0 < r := by
    refine div_pos ?_ hpow_pos
    exact mul_pos (by exact_mod_cast Omega.maxFiberMultiplicity_ge_one m) hn_pos
  have hw_nonneg : ∀ x, 0 ≤ w x := by
    intro x
    exact div_nonneg (by exact_mod_cast (Nat.zero_le (Omega.X.fiberMultiplicity x))) (by positivity)
  have hw_pos : ∀ x, 0 < w x := by
    intro x
    exact div_pos (by exact_mod_cast Omega.X.fiberMultiplicity_pos x) (by positivity)
  have hu_pos : ∀ x, 0 < u x := by
    intro x
    exact one_div_pos.mpr hn_pos
  have hw_sum : ∑ x : Omega.X m, w x = 1 := by
    calc
      ∑ x : Omega.X m, w x =
          (∑ x : Omega.X m, Omega.X.fiberMultiplicity x) / (2 ^ m : ℕ) := by
            simp [w, pom_wm_kl_to_uniform_pushforward, Finset.sum_div]
      _ = ((2 ^ m : ℕ) : ℝ) / (2 ^ m : ℕ) := by
        congr 1
        exact_mod_cast Omega.X.fiberMultiplicity_sum_eq_pow m
      _ = 1 := by
        field_simp [show ((2 ^ m : ℕ) : ℝ) ≠ 0 by positivity]
  have hratio_le : ∀ x : Omega.X m, w x / u x ≤ r := by
    intro x
    have hmult_le : (Omega.X.fiberMultiplicity x : ℝ) ≤ Omega.X.maxFiberMultiplicity m := by
      exact_mod_cast Omega.X.fiberMultiplicity_le_max x
    have hpow_cast : (((2 ^ m : ℕ) : ℝ)) = (2 : ℝ) ^ m := by
      exact_mod_cast (show 2 ^ m = 2 ^ m by rfl)
    calc
      w x / u x = w x * n := by
        change w x / ((1 : ℝ) / n) = w x * n
        field_simp [hn_ne]
      _ = (Omega.X.fiberMultiplicity x : ℝ) * n / (2 : ℝ) ^ m := by
        rw [show w x = (Omega.X.fiberMultiplicity x : ℝ) / (2 : ℝ) ^ m by
          simp [w, pom_wm_kl_to_uniform_pushforward, hpow_cast]]
        ring
      _ ≤ (Omega.X.maxFiberMultiplicity m : ℝ) * n / (2 : ℝ) ^ m := by
        refine div_le_div_of_nonneg_right ?_ hpow_pos.le
        nlinarith [hn_pos, hmult_le]
      _ = r := by rfl
  have hpointwise :
      ∀ x : Omega.X m, w x * Real.log (w x / u x) ≤ w x * Real.log r := by
    intro x
    refine mul_le_mul_of_nonneg_left ?_ (hw_nonneg x)
    exact Real.log_le_log (div_pos (hw_pos x) (hu_pos x)) (hratio_le x)
  calc
    klDiv w u = ∑ x : Omega.X m, w x * Real.log (w x / u x) := by
      rfl
    _ ≤ ∑ x : Omega.X m, w x * Real.log r := Finset.sum_le_sum (fun x _ => hpointwise x)
    _ = (∑ x : Omega.X m, w x) * Real.log r := by rw [← Finset.sum_mul]
    _ = Real.log r := by rw [hw_sum, one_mul]
    _ = Real.log ((Omega.X.maxFiberMultiplicity m : ℝ) * Nat.fib (m + 2) / (2 : ℝ) ^ m) := by
      simp [r, n, Omega.X.card_eq_fib]

end

end Omega.POM
