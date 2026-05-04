import Mathlib.Tactic

/-- Paper label: `thm:xi-single-elliptic-zero-reconstructs-scale`. -/
theorem paper_xi_single_elliptic_zero_reconstructs_scale {K : Type*} [Field K]
    (u w r a : K) (hr : r ≠ 0) (ha : a = r + r⁻¹)
    (hrel : w^2 - a * u * w + (u^2 + (r - r⁻¹)^2) = 0) :
    a^2 - (u * w) * a + (w^2 + u^2 - 4) = 0 ∧ r^2 - a * r + 1 = 0 := by
  constructor
  · have hdiff : (r - r⁻¹)^2 = a^2 - 4 := by
      rw [ha]
      field_simp [hr]
      ring_nf
    rw [hdiff] at hrel
    have hrewrite :
        a^2 - (u * w) * a + (w^2 + u^2 - 4) =
          w^2 - a * u * w + (u^2 + (a^2 - 4)) := by
      ring
    rw [hrewrite]
    exact hrel
  · rw [ha]
    field_simp [hr]
    ring_nf
