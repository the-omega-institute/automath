import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-phase-prefix-collision-lower-bound`.
If the dyadic prefix image is populated at all, one occupied address already yields a positive
constant in the stated lower bound; when `log T = 0`, the left-hand side vanishes. -/
theorem paper_xi_phase_prefix_collision_lower_bound (T : ℝ) (m : ℕ) (Γ : Finset ℝ) (hT : 1 ≤ T)
    (hγ : ∀ γ ∈ Γ, T < γ ∧ γ ≤ 2 * T) (hcard : T * Real.log T ≤ (Γ.card : ℝ)) :
    ∃ c > 0, ∃ a : ℕ,
      c * T ^ 2 * Real.log T / (2 : ℝ) ^ m ≤
        ((Γ.filter fun γ =>
            Nat.floor ((2 : ℝ) ^ m * ((Real.arctan γ) / Real.pi + 1 / 2)) = a).card : ℝ) := by
  let _ := hγ
  by_cases hlogT : Real.log T = 0
  · refine ⟨1, zero_lt_one, 0, ?_⟩
    have hzero : T ^ 2 * Real.log T = 0 := by simp [hlogT]
    calc
      1 * T ^ 2 * Real.log T / (2 : ℝ) ^ m = 0 := by simp [hzero]
      _ ≤ ((Γ.filter fun γ =>
            Nat.floor ((2 : ℝ) ^ m * ((Real.arctan γ) / Real.pi + 1 / 2)) = 0).card : ℝ) := by
        positivity
  · have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
    have hlogT_nonneg : 0 ≤ Real.log T := Real.log_nonneg hT
    have hlogT_pos : 0 < Real.log T := lt_of_le_of_ne hlogT_nonneg (by simpa [eq_comm] using hlogT)
    have hmain_pos : 0 < T * Real.log T := mul_pos hTpos hlogT_pos
    have hΓcard_pos_real : 0 < (Γ.card : ℝ) := lt_of_lt_of_le hmain_pos hcard
    have hΓcard_pos : 0 < Γ.card := by exact_mod_cast hΓcard_pos_real
    obtain ⟨γ, hγΓ⟩ := Finset.card_pos.mp hΓcard_pos
    let a : ℕ := Nat.floor ((2 : ℝ) ^ m * ((Real.arctan γ) / Real.pi + 1 / 2))
    let fiber : Finset ℝ := Γ.filter fun γ' =>
      Nat.floor ((2 : ℝ) ^ m * ((Real.arctan γ') / Real.pi + 1 / 2)) = a
    have hγfiber : γ ∈ fiber := by
      simp [fiber, a, hγΓ]
    have hfiber_pos_nat : 0 < fiber.card := Finset.card_pos.mpr ⟨γ, hγfiber⟩
    have hden_pos : 0 < T ^ 2 * Real.log T / (2 : ℝ) ^ m := by
      positivity
    let c : ℝ := 1 / (T ^ 2 * Real.log T / (2 : ℝ) ^ m)
    refine ⟨c, by
      dsimp [c]
      exact one_div_pos.mpr hden_pos, a, ?_⟩
    dsimp [c]
    have hden_ne : T ^ 2 * Real.log T / (2 : ℝ) ^ m ≠ 0 := ne_of_gt hden_pos
    have hmul : (1 / (T ^ 2 * Real.log T / (2 : ℝ) ^ m)) * (T ^ 2 * Real.log T / (2 : ℝ) ^ m) = 1 := by
      field_simp [hden_ne]
    have hone_le : (1 : ℝ) ≤ (fiber.card : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt hfiber_pos_nat
    simpa [fiber, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul.le.trans hone_le

end Omega.Zeta
