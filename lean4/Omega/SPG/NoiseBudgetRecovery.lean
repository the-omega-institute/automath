import Mathlib.Tactic

namespace Omega.SPG

/-- Divide a positive-factor inequality through by the factor.
    cor:spg-dyadic-holographic-reconstruction-noise-budget -/
theorem le_div_of_pos_mul_le {c ε δ : ℝ} (hc : 0 < c) (h : c * ε ≤ δ) :
    ε ≤ δ / c := by
  exact (le_div_iff₀ hc).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using h)

/-- Rearrangement equivalence for positive factors.
    cor:spg-dyadic-holographic-reconstruction-noise-budget -/
theorem pos_mul_le_iff_le_div {c ε δ : ℝ} (hc : 0 < c) :
    c * ε ≤ δ ↔ ε ≤ δ / c := by
  constructor
  · intro h
    exact le_div_of_pos_mul_le hc h
  · intro h
    have : ε * c ≤ δ := (le_div_iff₀ hc).1 h
    simpa [mul_comm] using this

/-- Reverse direction: ε ≤ δ/c → c·ε ≤ δ, for positive c.
    cor:spg-dyadic-holographic-reconstruction-noise-budget -/
theorem mul_le_of_le_div_pos {c ε δ : ℝ} (hc : 0 < c) (h : ε ≤ δ / c) :
    c * ε ≤ δ := (pos_mul_le_iff_le_div hc).mpr h

/-- Symmetric packaging of the positive-factor rearrangement.
    cor:spg-dyadic-holographic-reconstruction-noise-budget -/
theorem noiseBudget_recovery_symmetry {c ε δ : ℝ} (hc : 0 < c) :
    c * ε ≤ δ ↔ ε ≤ δ / c :=
  pos_mul_le_iff_le_div hc

/-- Contrapositive: δ/c < ε → δ < c·ε.
    cor:spg-dyadic-holographic-reconstruction-noise-budget -/
theorem noiseBudget_contrapositive {c ε δ : ℝ} (hc : 0 < c)
    (h : δ / c < ε) : δ < c * ε := by
  have hne : c ≠ 0 := ne_of_gt hc
  have hmul : δ < ε * c := (div_lt_iff₀ hc).1 h
  linarith [hmul]

/-- Strict rearrangement equivalence for positive factors.
    cor:spg-dyadic-holographic-reconstruction-noise-budget -/
theorem pos_mul_lt_iff_lt_div {c ε δ : ℝ} (hc : 0 < c) :
    c * ε < δ ↔ ε < δ / c := by
  constructor
  · intro h
    rw [lt_div_iff₀ hc]
    linarith
  · intro h
    have := (lt_div_iff₀ hc).1 h
    linarith

/-- Paper noise-budget algebra package.
    cor:spg-dyadic-holographic-reconstruction-noise-budget -/
theorem paper_noiseBudget_algebra_package :
    (∀ {c ε δ : ℝ}, 0 < c → (c * ε ≤ δ ↔ ε ≤ δ / c)) ∧
    (∀ {c ε δ : ℝ}, 0 < c → (c * ε < δ ↔ ε < δ / c)) ∧
    (∀ {c ε δ : ℝ}, 0 < c → c * ε ≤ δ → ε ≤ δ / c) ∧
    (∀ {c ε δ : ℝ}, 0 < c → ε ≤ δ / c → c * ε ≤ δ) :=
  ⟨@pos_mul_le_iff_le_div,
   @pos_mul_lt_iff_lt_div,
   @le_div_of_pos_mul_le,
   @mul_le_of_le_div_pos⟩

end Omega.SPG
