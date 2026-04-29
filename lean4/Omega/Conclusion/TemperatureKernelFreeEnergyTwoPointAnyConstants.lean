import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

theorem paper_conclusion_temperature_kernel_free_energy_two_point_any_constants
    (a b F0 F1 : ℝ) (hgap : F0 < F1) (hab : a < b) :
    ∃ k : ℕ, ∃ d : ℝ, max a ((k : ℝ) * F0 + d) = a ∧ max a ((k : ℝ) * F1 + d) = b := by
  have hgap_pos : 0 < F1 - F0 := sub_pos.mpr hgap
  let k : ℕ := Nat.ceil ((b - a) / (F1 - F0))
  let d : ℝ := b - (k : ℝ) * F1
  refine ⟨k, d, ?_, ?_⟩
  · apply max_eq_left
    have hkceil : (b - a) / (F1 - F0) ≤ (k : ℝ) := Nat.le_ceil ((b - a) / (F1 - F0))
    have hk_mul : b - a ≤ (k : ℝ) * (F1 - F0) := (div_le_iff₀ hgap_pos).mp hkceil
    dsimp [d]
    linarith
  · have hd_eq : (k : ℝ) * F1 + d = b := by
      dsimp [d]
      ring
    rw [hd_eq]
    exact max_eq_right hab.le

end Omega.Conclusion
