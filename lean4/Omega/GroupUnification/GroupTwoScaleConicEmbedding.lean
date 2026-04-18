import Mathlib.Tactic

namespace Omega.GroupUnification

/-- Solving the two-scale linear system for `(z, z⁻¹)` forces the Joukowsky coordinates to lie on
the conic cut out by the determinant identity, and recovers `z` explicitly.
    thm:group-two-scale-conic-embedding -/
theorem paper_group_two_scale_conic_embedding {K : Type*} [Field K] (r1 r2 z : K)
    (hr1 : r1 ≠ 0) (hr2 : r2 ≠ 0) (hr : r1 ^ 2 ≠ r2 ^ 2) (hz : z ≠ 0) :
    let w1 := r1 * z + r1⁻¹ * z⁻¹
    let w2 := r2 * z + r2⁻¹ * z⁻¹
    r1 * r2 * (r1 * w1 - r2 * w2) * (r1 * w2 - r2 * w1) = (r1 ^ 2 - r2 ^ 2) ^ 2 ∧
      z = (r1 * w1 - r2 * w2) / (r1 ^ 2 - r2 ^ 2) := by
  dsimp
  have hdet : r1 ^ 2 - r2 ^ 2 ≠ 0 := sub_ne_zero.mpr hr
  have hlin1 :
      r1 * (r1 * z + r1⁻¹ * z⁻¹) - r2 * (r2 * z + r2⁻¹ * z⁻¹) = (r1 ^ 2 - r2 ^ 2) * z := by
    calc
      r1 * (r1 * z + r1⁻¹ * z⁻¹) - r2 * (r2 * z + r2⁻¹ * z⁻¹)
          = (r1 ^ 2 * z + z⁻¹) - (r2 ^ 2 * z + z⁻¹) := by
              simp [pow_two, hr1, hr2, mul_add, mul_left_comm, mul_comm]
      _ = (r1 ^ 2 - r2 ^ 2) * z := by ring
  have hlin2 :
      r1 * r2 * (r1 * (r2 * z + r2⁻¹ * z⁻¹) - r2 * (r1 * z + r1⁻¹ * z⁻¹)) =
        (r1 ^ 2 - r2 ^ 2) * z⁻¹ := by
    calc
      r1 * r2 * (r1 * (r2 * z + r2⁻¹ * z⁻¹) - r2 * (r1 * z + r1⁻¹ * z⁻¹))
          = r1 * r2 * ((r1 * r2) * z + (r1 * r2⁻¹) * z⁻¹ - ((r2 * r1) * z + (r2 * r1⁻¹) * z⁻¹)) := by
              ring_nf
      _ = r1 * r2 * ((r1 * r2⁻¹ - r2 * r1⁻¹) * z⁻¹) := by ring
      _ = (r1 ^ 2 - r2 ^ 2) * z⁻¹ := by
            field_simp [pow_two, hr1, hr2]
  refine ⟨?_, ?_⟩
  · calc
      r1 * r2 * (r1 * (r1 * z + r1⁻¹ * z⁻¹) - r2 * (r2 * z + r2⁻¹ * z⁻¹)) *
          (r1 * (r2 * z + r2⁻¹ * z⁻¹) - r2 * (r1 * z + r1⁻¹ * z⁻¹))
          = (r1 * (r1 * z + r1⁻¹ * z⁻¹) - r2 * (r2 * z + r2⁻¹ * z⁻¹)) *
              (r1 * r2 * (r1 * (r2 * z + r2⁻¹ * z⁻¹) - r2 * (r1 * z + r1⁻¹ * z⁻¹))) := by
                ring
      _ = ((r1 ^ 2 - r2 ^ 2) * z) * ((r1 ^ 2 - r2 ^ 2) * z⁻¹) := by
            rw [hlin1, hlin2]
      _ = (r1 ^ 2 - r2 ^ 2) ^ 2 := by
            field_simp [hz]
  · calc
      z = ((r1 ^ 2 - r2 ^ 2) * z) / (r1 ^ 2 - r2 ^ 2) := by
            field_simp [hdet]
      _ = (r1 * (r1 * z + r1⁻¹ * z⁻¹) - r2 * (r2 * z + r2⁻¹ * z⁻¹)) / (r1 ^ 2 - r2 ^ 2) := by
            rw [hlin1]

end Omega.GroupUnification
