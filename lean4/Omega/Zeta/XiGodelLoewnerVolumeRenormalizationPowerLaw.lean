import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:xi-godel-loewner-volume-renormalization-power-law`. Solving the `t = 1`
volume formula for the product term and substituting it into the general `t` formula gives the
power-law renormalization. -/
theorem paper_xi_godel_loewner_volume_renormalization_power_law
    (Vkt Vk1 Ckt Ck P : ℝ) (e : ℕ) (hCk : Ck ≠ 0) (h1 : Vk1 = Ck * P)
    (ht : Vkt = Ckt * P ^ e) :
    Vkt = Ckt * (Vk1 / Ck) ^ e := by
  have hP : Vk1 / Ck = P := by
    rw [h1]
    field_simp [hCk]
  rw [ht, hP]

end Omega.Zeta
