import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

namespace Omega.Folding

noncomputable section

/-- Concrete data for a global lower bound on the gap between two fold-resonance zero candidates
of the form `(K / 2) φ^m` and `(L / 2) φ^n`. The hypothesis `norm_gap_lower` is the explicit
estimate on `|K - L φ^(n-m)|` obtained from the nonzero algebraic-integer norm in the conjugate
embedding. -/
structure fold_resonance_min_gap_global_lower_data where
  K : ℕ
  L : ℕ
  m : ℕ
  n : ℕ
  hK : 0 < K
  hL : 0 < L
  hmn : m ≤ n
  norm_gap_lower :
    1 / ((K : ℝ) + (L : ℝ)) ≤
      |(K : ℝ) - (L : ℝ) * Real.goldenRatio ^ (n - m)|

namespace fold_resonance_min_gap_global_lower_data

/-- First explicit zero candidate. -/
def u (D : fold_resonance_min_gap_global_lower_data) : ℝ :=
  ((D.K : ℝ) / 2) * Real.goldenRatio ^ D.m

/-- Second explicit zero candidate. -/
def v (D : fold_resonance_min_gap_global_lower_data) : ℝ :=
  ((D.L : ℝ) / 2) * Real.goldenRatio ^ D.n

/-- Global lower bound obtained after translating the algebraic estimate into the physical scale
of the zeros. -/
def delta (D : fold_resonance_min_gap_global_lower_data) : ℝ :=
  ((1 : ℝ) / 2) * Real.goldenRatio ^ D.m / ((D.K : ℝ) + (D.L : ℝ))

/-- Paper-facing global gap statement. -/
def statement (D : fold_resonance_min_gap_global_lower_data) : Prop :=
  D.delta ≤ |D.u - D.v| ∧ 0 < |D.u - D.v|

lemma u_sub_v_factorization (D : fold_resonance_min_gap_global_lower_data) :
    D.u - D.v =
      ((1 : ℝ) / 2) * Real.goldenRatio ^ D.m *
        ((D.K : ℝ) - (D.L : ℝ) * Real.goldenRatio ^ (D.n - D.m)) := by
  have hn : D.n = D.m + (D.n - D.m) := (Nat.add_sub_of_le D.hmn).symm
  have hpow :
      Real.goldenRatio ^ D.n =
        Real.goldenRatio ^ D.m * Real.goldenRatio ^ (D.n - D.m) := by
    rw [hn]
    simpa using (pow_add Real.goldenRatio D.m (D.n - D.m))
  unfold u v
  rw [hpow]
  ring

lemma abs_u_sub_v (D : fold_resonance_min_gap_global_lower_data) :
    |D.u - D.v| =
      ((1 : ℝ) / 2) * Real.goldenRatio ^ D.m *
        |(D.K : ℝ) - (D.L : ℝ) * Real.goldenRatio ^ (D.n - D.m)| := by
  rw [D.u_sub_v_factorization, abs_mul, abs_mul]
  have hpow_nonneg : 0 ≤ Real.goldenRatio ^ D.m := by positivity
  simp [abs_of_nonneg hpow_nonneg]

lemma delta_pos (D : fold_resonance_min_gap_global_lower_data) : 0 < D.delta := by
  unfold delta
  have hnum : 0 < ((1 : ℝ) / 2) * Real.goldenRatio ^ D.m := by positivity
  have hK_real : 0 < (D.K : ℝ) := by exact_mod_cast D.hK
  have hL_real : 0 < (D.L : ℝ) := by exact_mod_cast D.hL
  have hden : 0 < (D.K : ℝ) + (D.L : ℝ) := add_pos hK_real hL_real
  exact div_pos hnum hden

end fold_resonance_min_gap_global_lower_data

open fold_resonance_min_gap_global_lower_data

/-- Paper label: `prop:fold-resonance-min-gap-global-lower`. -/
theorem paper_fold_resonance_min_gap_global_lower
    (D : fold_resonance_min_gap_global_lower_data) : D.statement := by
  have hscale_pos : 0 < ((1 : ℝ) / 2) * Real.goldenRatio ^ D.m := by positivity
  have hscaled :=
    mul_le_mul_of_nonneg_left D.norm_gap_lower (le_of_lt hscale_pos)
  have hbound : D.delta ≤ |D.u - D.v| := by
    rw [D.abs_u_sub_v]
    simpa [fold_resonance_min_gap_global_lower_data.delta, div_eq_mul_inv, mul_assoc,
      mul_left_comm, mul_comm] using hscaled
  exact ⟨hbound, lt_of_lt_of_le D.delta_pos hbound⟩

end

end Omega.Folding
