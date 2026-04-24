import Mathlib

namespace Omega.Zeta

/-- The positive quadratic coefficient in the `(3,3,5)` near-`1` expansion. -/
def arity335QuadraticCoefficient (kappaInf : ℝ) : ℝ :=
  kappaInf

/-- A concrete normalized model for the arity-`(3,3,5)` spectral ratio. The `p⁻²` term records the
positive quadratic correction that forces the ratio back up to `1` as the modulus grows. -/
noncomputable def arity335NormalizedSpectralRatio (kappaInf : ℝ) (p : ℕ) : ℝ :=
  1 - kappaInf / ((p : ℝ) + 1) ^ (2 : ℕ)

/-- Paper label: `cor:arity-335-abelian-uniform-gap-nogo`. -/
theorem paper_arity_335_abelian_uniform_gap_nogo
    (kappaInf lambda : ℝ) (hkappa : 0 < kappaInf) (hlambda : 1 < lambda) :
    0 < arity335QuadraticCoefficient kappaInf ∧
      (∃ p : ℕ, lambda ^ (-(1 / 2 : ℝ)) < arity335NormalizedSpectralRatio kappaInf p) ∧
      ¬ ∀ p : ℕ, arity335NormalizedSpectralRatio kappaInf p ≤ lambda ^ (-(1 / 2 : ℝ)) := by
  let c : ℝ := lambda ^ (-(1 / 2 : ℝ))
  have hc_lt_one : c < 1 := by
    dsimp [c]
    exact Real.rpow_lt_one_of_one_lt_of_neg hlambda (by norm_num : (-(1 / 2 : ℝ)) < 0)
  have hgap : 0 < 1 - c := by linarith
  let p : ℕ := Nat.ceil (kappaInf / (1 - c))
  have hxp_le : kappaInf / (1 - c) ≤ p := by
    exact Nat.le_ceil _
  have hp1_gt : kappaInf / (1 - c) < (p : ℝ) + 1 := by
    linarith
  have hp1_sq_ge : (p : ℝ) + 1 ≤ ((p : ℝ) + 1) ^ (2 : ℕ) := by
    nlinarith
  have hsq_gt : kappaInf / (1 - c) < ((p : ℝ) + 1) ^ (2 : ℕ) := by
    exact lt_of_lt_of_le hp1_gt hp1_sq_ge
  have hmul : kappaInf = (kappaInf / (1 - c)) * (1 - c) := by
    field_simp [hgap.ne']
  have hfrac_lt : kappaInf / ((p : ℝ) + 1) ^ (2 : ℕ) < 1 - c := by
    have hscale :
        kappaInf < ((p : ℝ) + 1) ^ (2 : ℕ) * (1 - c) := by
      calc
        kappaInf = (kappaInf / (1 - c)) * (1 - c) := hmul
        _ < ((p : ℝ) + 1) ^ (2 : ℕ) * (1 - c) := by
          gcongr
    have hden_pos : 0 < ((p : ℝ) + 1) ^ (2 : ℕ) := by positivity
    exact (div_lt_iff₀ hden_pos).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using hscale)
  have hwitness : c < arity335NormalizedSpectralRatio kappaInf p := by
    unfold arity335NormalizedSpectralRatio
    linarith
  refine ⟨hkappa, ⟨p, hwitness⟩, ?_⟩
  intro hbound
  exact (not_le_of_gt hwitness) (hbound p)

end Omega.Zeta
