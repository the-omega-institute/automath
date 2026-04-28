import Mathlib.Tactic

namespace Omega

/-- Paper label: `thm:pom-anom-coprime-two-point-test`. -/
theorem paper_pom_anom_coprime_two_point_test {H : Type*} [AddCommGroup H] (anom : H)
    (q1 q2 : ℤ) (hbez : ∃ u v : ℤ, u * q1 + v * q2 = 1) (h1 : q1 • anom = 0)
    (h2 : q2 • anom = 0) : anom = 0 := by
  rcases hbez with ⟨u, v, huv⟩
  have hzero : (u * q1 + v * q2) • anom = 0 := by
    rw [add_zsmul, mul_zsmul, mul_zsmul]
    simp [h1, h2]
  simpa [huv] using hzero

end Omega
