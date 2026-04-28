import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:near1-kappa-infty-c1-transcendence-obstruction`. If `c1^2` is
transcendental while every quotient `kappa / a` by a nonzero algebraic `a` is not, then no
nonzero algebraic scalar can satisfy `kappa = a * c1^2`. -/
theorem paper_near1_kappa_infty_c1_transcendence_obstruction
    (TranscendentalOverQ AlgebraicOverQ : ℝ → Prop) (c1 kappa : ℝ)
    (htrans_sq : TranscendentalOverQ (c1 ^ 2)) (hkappa_alg : AlgebraicOverQ kappa)
    (hkappa_ne : kappa ≠ 0)
    (halg_div_not_trans :
      ∀ a : ℝ, AlgebraicOverQ a → a ≠ 0 → ¬ TranscendentalOverQ (kappa / a)) :
    ∀ a : ℝ, AlgebraicOverQ a → a ≠ 0 → kappa ≠ a * c1 ^ 2 := by
  have _ : AlgebraicOverQ kappa := hkappa_alg
  have _ : kappa ≠ 0 := hkappa_ne
  intro a ha_alg ha_ne hkappa_eq
  have hquot : kappa / a = c1 ^ 2 := by
    rw [hkappa_eq]
    field_simp [ha_ne]
  exact (halg_div_not_trans a ha_alg ha_ne) (by simpa [← hquot] using htrans_sq)

end Omega.Zeta
