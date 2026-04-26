import Mathlib.Tactic

set_option linter.unusedVariables false

namespace Omega.POM

/-- Paper label: `cor:pom-query-distortion-zero-bit-corridor`. -/
theorem paper_pom_query_distortion_zero_bit_corridor
    {β δ p2 R : ℝ} {bcrit : ℝ → ℝ → ℝ}
    (hzero : (δ ≥ 1 - p2 ↔ R = 0))
    (hplane : ∀ β, 0 ≤ β → β < 1 → bcrit β δ = R / (1 - β))
    (hpos : δ < 1 - p2 → 0 < R) :
    (δ ≥ 1 - p2 → R = 0 ∧ ∀ β, 0 ≤ β → β < 1 → bcrit β δ = 0) ∧
      (δ < 1 - p2 → 0 < R ∧ ∀ β, 0 ≤ β → β < 1 → 0 < bcrit β δ) := by
  constructor
  · intro hδ
    have hR : R = 0 := hzero.mp hδ
    refine ⟨hR, ?_⟩
    intro β hβ0 hβ1
    rw [hplane β hβ0 hβ1, hR]
    simp
  · intro hδ
    have hR : 0 < R := hpos hδ
    refine ⟨hR, ?_⟩
    intro β hβ0 hβ1
    rw [hplane β hβ0 hβ1]
    exact div_pos hR (sub_pos.mpr hβ1)

/-- Paper label: `cor:pom-query-distortion-zero-bit-threshold-auditable`. -/
theorem paper_pom_query_distortion_zero_bit_threshold_auditable
    {m : ℕ} {S2 Col delta0 : ℝ}
    (hCol : Col = S2 / (2 : ℝ) ^ (2 * m))
    (hdelta0 : delta0 = 1 - Col) :
    delta0 = 1 - S2 / (2 : ℝ) ^ (2 * m) := by
  rw [hdelta0, hCol]

end Omega.POM
