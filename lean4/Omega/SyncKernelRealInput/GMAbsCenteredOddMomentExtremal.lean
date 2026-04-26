import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.SyncKernelRealInput

open scoped BigOperators

noncomputable section

/-- The absolute centered odd moment of a two-level profile with top deviation `δ` and lower
deviations `rest`. The ambient matrix size is `m = rest.card + 1`. -/
def gm_abs_centered_odd_moment_extremal_moment
    {n : ℕ} (δ : ℝ) (rest : Fin n → ℝ) (k : ℕ) : ℝ :=
  δ ^ (2 * k + 1) + ∑ i, |rest i| ^ (2 * k + 1)

/-- Paper label: `thm:gm-abs-centered-odd-moment-extremal`.
For a centered spectrum with top deviation `δ ≥ 0` and remaining deviations summing to `-δ`, the
absolute odd central moment controls the extremal spike by the sharp two-level lower envelope
`(1 + (m - 1)^(-2k)) δ^(2k+1)`. -/
theorem paper_gm_abs_centered_odd_moment_extremal
    (m k : ℕ) (hm : 2 ≤ m) (mean δ : ℝ) (rest : Fin (m - 1) → ℝ)
    (hδ : 0 ≤ δ) (hsum : ∑ i, rest i = -δ) :
    let lambdaMax : ℝ := mean + δ
    let A := gm_abs_centered_odd_moment_extremal_moment δ rest k
    lambdaMax - mean = δ ∧
      (1 + 1 / (((m - 1 : ℕ) : ℝ) ^ (2 * k)) ) * δ ^ (2 * k + 1) ≤ A := by
  dsimp [gm_abs_centered_odd_moment_extremal_moment]
  have hm1_nat : 0 < m - 1 := by omega
  have hm1_real : 0 < (((m - 1 : ℕ) : ℝ)) := by
    exact_mod_cast hm1_nat
  have hsum_abs : δ ≤ ∑ i, |rest i| := by
    calc
      δ = |∑ i, rest i| := by rw [hsum, abs_neg, abs_of_nonneg hδ]
      _ ≤ ∑ i, |rest i| := by
        simpa using (Finset.abs_sum_le_sum_abs (s := Finset.univ) (f := rest))
  have hpow_le : δ ^ (2 * k + 1) ≤ (∑ i, |rest i|) ^ (2 * k + 1) := by
    gcongr
  have hjensen := pow_sum_div_card_le_sum_pow (s := (Finset.univ : Finset (Fin (m - 1))))
    (f := fun i => |rest i|) (hf := by
      intro i hi
      exact abs_nonneg _) (n := 2 * k)
  have hjensen' :
      (∑ i, |rest i|) ^ (2 * k + 1) / (((m - 1 : ℕ) : ℝ) ^ (2 * k)) ≤
        ∑ i, |rest i| ^ (2 * k + 1) := by
    simpa [Fintype.card_fin, hm1_nat] using hjensen
  have hdiv_le : δ ^ (2 * k + 1) / (((m - 1 : ℕ) : ℝ) ^ (2 * k)) ≤
      ∑ i, |rest i| ^ (2 * k + 1) := by
    exact le_trans (by gcongr) hjensen'
  have hfactor :
      (1 + 1 / (((m - 1 : ℕ) : ℝ) ^ (2 * k))) * δ ^ (2 * k + 1) =
        δ ^ (2 * k + 1) + δ ^ (2 * k + 1) / (((m - 1 : ℕ) : ℝ) ^ (2 * k)) := by
    have hm1_ne : (((m - 1 : ℕ) : ℝ) ^ (2 * k)) ≠ 0 := by positivity
    field_simp [hm1_ne]
  constructor
  · ring
  rw [hfactor]
  gcongr

end

end Omega.SyncKernelRealInput
