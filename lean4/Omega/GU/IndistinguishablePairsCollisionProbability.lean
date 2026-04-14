import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic
import Omega.GU.FixedPrecisionExponentialMultiplicity

namespace Omega.GU

set_option maxHeartbeats 400000 in
/-- Paper-facing wrapper: once a fixed-precision bucket contains at least `L` states, it carries
at least `Nat.choose L 2` indistinguishable unordered pairs, and the normalized square occupancy
of that bucket gives the corresponding iid collision-probability lower bound.
    prop:group-jg-indistinguishable-pairs-and-collision-probability -/
theorem paper_gut_indistinguishable_pairs_and_collision_probability
    (k m L : ℕ)
    (bucket : Finset (Fin k) → Fin m)
    (hm : 0 < m)
    (hL : L * m ≤ 2 ^ k) :
    ∃ y : Fin m,
      L ≤ Fintype.card {s : Finset (Fin k) // bucket s = y} ∧
      Nat.choose L 2 ≤ Nat.choose (Fintype.card {s : Finset (Fin k) // bucket s = y}) 2 ∧
      (((L : ℝ) / (2 ^ k : ℝ)) ^ 2 ≤
        ((Fintype.card {s : Finset (Fin k) // bucket s = y} : ℝ) / (2 ^ k : ℝ)) ^ 2) := by
  classical
  let fiberCard : Fin m → ℕ := fun y =>
    Fintype.card {s : Finset (Fin k) // bucket s = y}
  obtain ⟨y, hy⟩ := paper_gut_fixed_precision_exponential_multiplicity k m bucket hm
  have hL' : m * L ≤ 2 ^ k := by
    simpa [Nat.mul_comm] using hL
  have hLy : L ≤ fiberCard y := by
    exact Nat.le_of_mul_le_mul_left (le_trans hL' hy) hm
  have hChoose : Nat.choose L 2 ≤ Nat.choose (fiberCard y) 2 :=
    Nat.choose_le_choose 2 hLy
  have hRatio :
      (L : ℝ) / (2 ^ k : ℝ) ≤ (fiberCard y : ℝ) / (2 ^ k : ℝ) := by
    have hLyReal : (L : ℝ) ≤ fiberCard y := by
      exact_mod_cast hLy
    have hInvNonneg : 0 ≤ ((2 ^ k : ℝ)⁻¹) := by positivity
    simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_right hLyReal hInvNonneg
  have hRatioSq :
      ((L : ℝ) / (2 ^ k : ℝ)) ^ 2 ≤ ((fiberCard y : ℝ) / (2 ^ k : ℝ)) ^ 2 := by
    have hNonneg : 0 ≤ (L : ℝ) / (2 ^ k : ℝ) := by positivity
    nlinarith
  exact ⟨y, by simpa [fiberCard] using hLy, by simpa [fiberCard] using hChoose,
    by simpa [fiberCard] using hRatioSq⟩

end Omega.GU
