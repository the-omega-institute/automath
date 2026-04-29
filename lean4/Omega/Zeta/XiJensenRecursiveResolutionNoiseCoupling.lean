import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-jensen-recursive-resolution-noise-coupling`. For the centered single-atom
Jensen profile `J(y) = (y - x)_+`, the ideal three-point trigger at scale `h` is exactly `h`. Any
noise bounded by `4 ε` still triggers when `ε < h / 4`, the extremal choice `η = -4 ε` shows
sharpness at and above the threshold, and the same trigger condition is equivalent after the
dyadic recursion `(h, ε) ↦ (h / 2, ε / 2)`. -/
theorem paper_xi_jensen_recursive_resolution_noise_coupling
    (x h ε : ℝ) (hh : 0 < h) :
    let J : ℝ → ℝ := fun y => max (y - x) 0
    let ideal := J (x + h) - 2 * J x + J (x - h)
    ideal = h ∧
      (ε < h / 4 → ∀ η : ℝ, |η| ≤ 4 * ε → 0 < ideal + η) ∧
      (h / 4 ≤ ε → ∃ η : ℝ, |η| ≤ 4 * ε ∧ ideal + η ≤ 0) ∧
      ((ε / 2 < (h / 2) / 4) ↔ ε < h / 4) := by
  dsimp
  have hJ_pos : max (x + h - x) 0 = h := by
    have hh' : 0 ≤ h := le_of_lt hh
    simp [hh']
  have hJ_zero : max (x - x) 0 = 0 := by simp
  have hJ_neg : max (x - h - x) 0 = 0 := by
    have hh' : 0 ≤ h := le_of_lt hh
    simp [hh']
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc
      max (x + h - x) 0 - 2 * max (x - x) 0 + max (x - h - x) 0
          = h - 2 * 0 + 0 := by rw [hJ_pos, hJ_zero, hJ_neg]
      _ = h := by ring
  · intro hε η hη
    have hη_lower : -(4 * ε) ≤ η := (abs_le.mp hη).1
    have hbound : 0 < h - 4 * ε := by
      nlinarith
    nlinarith
  · intro hε
    refine ⟨-4 * ε, ?_, ?_⟩
    · have hε_nonneg : 0 ≤ ε := by
        have : 0 < h / 4 := by positivity
        linarith
      have habs : |-4 * ε| = 4 * ε := by
        have hnonpos : -4 * ε ≤ 0 := by
          nlinarith
        rw [abs_of_nonpos hnonpos]
        nlinarith
      rw [habs]
    · nlinarith
  · constructor <;> intro hε <;> nlinarith

end Omega.Zeta
