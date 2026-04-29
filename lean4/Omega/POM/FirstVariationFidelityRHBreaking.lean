import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

namespace Omega.POM

theorem paper_pom_first_variation_fidelity_rh_breaking (a : Nat) (rho eta : Real)
    (Faithful BreaksRH : Nat → Prop) (ha : 1 ≤ a) (hrho : 1 < rho) (heta : 0 < eta)
    (hspectral : ∀ b, 2 ≤ b → Faithful b →
      eta * rho ^ (b - 1) > rho ^ (b / 2) → BreaksRH b) :
    ∃ b0, 2 ≤ b0 ∧ ∀ b, b0 ≤ b → Faithful b → BreaksRH b := by
  have _ : 1 ≤ a := ha
  have hrho_pos : 0 < rho := lt_trans zero_lt_one hrho
  have hrho_one : 1 ≤ rho := le_of_lt hrho
  obtain ⟨N, hN⟩ :=
    Filter.eventually_atTop.1
      ((tendsto_pow_atTop_atTop_of_one_lt hrho).eventually_gt_atTop eta⁻¹)
  have hNbig : eta⁻¹ < rho ^ N := hN N le_rfl
  have hNscaled : 1 < eta * rho ^ N := by
    calc
      1 = eta * eta⁻¹ := by rw [mul_inv_cancel₀ heta.ne']
      _ < eta * rho ^ N := mul_lt_mul_of_pos_left hNbig heta
  refine ⟨2 * N + 2, by omega, ?_⟩
  intro b hb hfaithful
  have hb_two : 2 ≤ b := by omega
  refine hspectral b hb_two hfaithful ?_
  let k := b - 1 - b / 2
  have hNle : N ≤ k := by
    dsimp [k]
    omega
  have hpowN_le : rho ^ N ≤ rho ^ k := pow_le_pow_right₀ hrho_one hNle
  have hk_scaled : 1 < eta * rho ^ k :=
    hNscaled.trans_le (mul_le_mul_of_nonneg_left hpowN_le heta.le)
  have hsplit : b / 2 + k = b - 1 := by
    dsimp [k]
    omega
  have hpowsplit : rho ^ (b - 1) = rho ^ (b / 2) * rho ^ k := by
    rw [← pow_add, hsplit]
  calc
    eta * rho ^ (b - 1) = rho ^ (b / 2) * (eta * rho ^ k) := by
      rw [hpowsplit]
      ring
    _ > rho ^ (b / 2) * 1 := mul_lt_mul_of_pos_left hk_scaled (pow_pos hrho_pos _)
    _ = rho ^ (b / 2) := by rw [mul_one]

end Omega.POM
