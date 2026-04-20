import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

namespace Omega.Zeta

/-- The two odd-square nodes produced by the symmetric-visibility specialization `κ = -1`. -/
def xiLeyangTwoLeadingNode (k : Fin 2) : ℚ :=
  ((2 * (k : ℕ) + 1 : ℚ) ^ 2)

/-- Concrete two-point expansion data for the leading Lee-Yang zeros near `u_c`.
The sample at node `k = 0, 1` has the shape `u_c - C * (2k + 1)^2 / n^2 + tail_k / n^3`. -/
structure XiLeyangTwoLeadingZerosExtrapolateData where
  n : ℚ
  hn : n ≠ 0
  u_c : ℚ
  C : ℚ
  tail : Fin 2 → ℚ
  sample : Fin 2 → ℚ
  hsample :
    ∀ k, sample k = u_c - xiLeyangTwoLeadingNode k * C / n ^ 2 + tail k / n ^ 3

namespace XiLeyangTwoLeadingZerosExtrapolateData

/-- The two-zero extrapolated center. -/
def centerEstimate (D : XiLeyangTwoLeadingZerosExtrapolateData) : ℚ :=
  (9 * D.sample 0 - D.sample 1) / 8

/-- The amplitude read off from the sample difference. -/
def amplitudeEstimate (D : XiLeyangTwoLeadingZerosExtrapolateData) : ℚ :=
  D.n ^ 2 / 8 * (D.sample 0 - D.sample 1)

/-- The amplitude read off after first eliminating the center. -/
def eliminatedAmplitudeEstimate (D : XiLeyangTwoLeadingZerosExtrapolateData) : ℚ :=
  -D.n ^ 2 * (D.sample 0 - D.centerEstimate)

/-- The surviving center error term after the `1` and `9` cancellation. -/
def centerTail (D : XiLeyangTwoLeadingZerosExtrapolateData) : ℚ :=
  (9 * D.tail 0 - D.tail 1) / (8 * D.n ^ 3)

/-- The surviving amplitude error term after multiplying by `n^2`. -/
def amplitudeTail (D : XiLeyangTwoLeadingZerosExtrapolateData) : ℚ :=
  (D.tail 0 - D.tail 1) / (8 * D.n)

/-- The `k = 0, 1` odd-square extrapolation recovers the center and the amplitude up to the
expected `n⁻³` and `n⁻¹` residual terms. -/
def extrapolatesCenterAndAmplitude (D : XiLeyangTwoLeadingZerosExtrapolateData) : Prop :=
  D.centerEstimate = D.u_c + D.centerTail ∧
    D.amplitudeEstimate = D.C + D.amplitudeTail ∧
      D.eliminatedAmplitudeEstimate = D.C + D.amplitudeTail

end XiLeyangTwoLeadingZerosExtrapolateData

open XiLeyangTwoLeadingZerosExtrapolateData

/-- Paper label: `cor:xi-leyang-two-leading-zeros-extrapolate-uc`.
At the symmetric-visibility nodes `1` and `9`, the linear combination `(9 u₀ - u₁) / 8`
eliminates the `C / n²` term, while both amplitude formulas recover `C` with the same
residual `n⁻¹` contribution. -/
theorem paper_xi_leyang_two_leading_zeros_extrapolate_uc
    (D : XiLeyangTwoLeadingZerosExtrapolateData) : D.extrapolatesCenterAndAmplitude := by
  have hn2 : D.n ^ 2 ≠ 0 := pow_ne_zero 2 D.hn
  have hn3 : D.n ^ 3 ≠ 0 := pow_ne_zero 3 D.hn
  have h0 := D.hsample 0
  have h1 := D.hsample 1
  norm_num [xiLeyangTwoLeadingNode] at h0 h1
  refine ⟨?_, ?_, ?_⟩
  · rw [centerEstimate, centerTail]
    simp [h0, h1]
    field_simp [hn2, hn3]
    ring
  · rw [amplitudeEstimate, amplitudeTail]
    simp [h0, h1]
    field_simp [hn2, hn3, D.hn]
    ring
  · rw [eliminatedAmplitudeEstimate, centerEstimate, amplitudeTail]
    simp [h0, h1]
    field_simp [hn2, hn3, D.hn]
    ring

end Omega.Zeta
