import Mathlib.Tactic

namespace Omega.Conclusion

/-- Solving the three asymptotic constants `(T₃, K₄, K₆)` recovers `μ₂`, `|μ₃|`, and `μ₄`.
    thm:conclusion-poisson-cauchy-three-constant-moment-tomography -/
theorem paper_conclusion_poisson_cauchy_three_constant_moment_tomography
    {T3 K4 K6 mu2 mu3 mu4 : Real} (hmu2 : 0 < mu2) (hT3 : T3 = |mu3| / Real.pi)
    (hK4 : K4 = mu2 ^ 2 / 8)
    (hK6 : K6 = mu2 ^ 3 / 64 - mu2 * mu4 / 8 + 3 * mu3 ^ 2 / 32) :
    mu2 = Real.sqrt (8 * K4) ∧
      |mu3| = Real.pi * T3 ∧
      mu4 =
        (3 * Real.pi ^ 2 * T3 ^ 2) / (4 * mu2) + mu2 ^ 2 / 8 - (8 * K6) / mu2 := by
  have hpi : (Real.pi : Real) ≠ 0 := by positivity
  have hmu2_ne : mu2 ≠ 0 := ne_of_gt hmu2
  have hden : (8 * mu2 : Real) ≠ 0 := by
    exact mul_ne_zero (show (8 : Real) ≠ 0 by norm_num) hmu2_ne
  have hmu2_eq : mu2 = Real.sqrt (8 * K4) := by
    rw [hK4]
    have hsq : 8 * (mu2 ^ 2 / 8) = mu2 ^ 2 := by ring
    rw [hsq, Real.sqrt_sq_eq_abs, abs_of_pos hmu2]
  have habs_mu3 : |mu3| = Real.pi * T3 := by
    calc
      |mu3| = Real.pi * (|mu3| / Real.pi) := by
        field_simp [hpi]
      _ = Real.pi * T3 := by rw [← hT3]
  have hmu3_sq : mu3 ^ 2 = Real.pi ^ 2 * T3 ^ 2 := by
    calc
      mu3 ^ 2 = |mu3| ^ 2 := by rw [sq_abs]
      _ = (Real.pi * T3) ^ 2 := by rw [habs_mu3]
      _ = Real.pi ^ 2 * T3 ^ 2 := by ring
  have hmu4_raw : mu4 = (mu2 ^ 3 + 6 * mu3 ^ 2 - 64 * K6) / (8 * mu2) := by
    rw [hK6]
    field_simp [hmu2_ne]
    ring
  have hmu4_eq :
      mu4 =
        (3 * Real.pi ^ 2 * T3 ^ 2) / (4 * mu2) + mu2 ^ 2 / 8 - (8 * K6) / mu2 := by
    rw [hmu4_raw, hmu3_sq]
    field_simp [hmu2_ne]
    ring
  exact ⟨hmu2_eq, habs_mu3, hmu4_eq⟩

/-- Equality of the two sixth-order jets for two nondegenerate generator directions recovers
    `μ₂`, `|μ₃|`, and `μ₄`.
    thm:conclusion-poisson-cauchy-sixth-universality-class -/
theorem paper_conclusion_poisson_cauchy_sixth_universality_class
    {mu2 mu2p mu3 mu3p mu4 mu4p K4 K4p T3 T3p Cf Cfp Cg Cgp f2 f3 g2 g3 :
      Real}
    (hmu2 : 0 < mu2) (hmu2p : 0 < mu2p)
    (hK4 : K4 = mu2 ^ 2 / 8) (hK4p : K4p = mu2p ^ 2 / 8)
    (hT3 : T3 = |mu3| / Real.pi) (hT3p : T3p = |mu3p| / Real.pi)
    (hCf : Cf = f2 * (3 * mu3 ^ 2 / 32 - mu2 * mu4 / 8) - f3 * mu2 ^ 3 / 64)
    (hCfp : Cfp = f2 * (3 * mu3p ^ 2 / 32 - mu2p * mu4p / 8) -
      f3 * mu2p ^ 3 / 64)
    (hCg : Cg = g2 * (3 * mu3 ^ 2 / 32 - mu2 * mu4 / 8) - g3 * mu2 ^ 3 / 64)
    (hCgp : Cgp = g2 * (3 * mu3p ^ 2 / 32 - mu2p * mu4p / 8) -
      g3 * mu2p ^ 3 / 64)
    (hdet : f2 * g3 - g2 * f3 ≠ 0)
    (hK : K4 = K4p) (hT : T3 = T3p) (hCfEq : Cf = Cfp) (hCgEq : Cg = Cgp) :
    mu2 = mu2p ∧ |mu3| = |mu3p| ∧ mu4 = mu4p := by
  have hpi : (Real.pi : Real) ≠ 0 := by positivity
  have hmu2_ne : mu2 ≠ 0 := ne_of_gt hmu2
  have hmu2_sq_eq : mu2 ^ 2 = mu2p ^ 2 := by
    nlinarith [hK4, hK4p, hK]
  have hmu2_eq : mu2 = mu2p := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hmu2_sq_eq with h | h
    · exact h
    · nlinarith [hmu2, hmu2p, h]
  have habs_mu3 : |mu3| = |mu3p| := by
    have hdiv : |mu3| / Real.pi = |mu3p| / Real.pi := by
      rw [← hT3, ← hT3p, hT]
    exact mul_right_cancel₀ hpi ((div_eq_div_iff hpi hpi).1 hdiv)
  have hmu3_sq_eq : mu3 ^ 2 = mu3p ^ 2 := by
    calc
      mu3 ^ 2 = |mu3| ^ 2 := by rw [sq_abs]
      _ = |mu3p| ^ 2 := by rw [habs_mu3]
      _ = mu3p ^ 2 := by rw [sq_abs]
  have hmu2p_pow : mu2p ^ 3 = mu2 ^ 3 := by
    rw [← hmu2_eq]
  have hf_system :
      f2 * ((3 * mu3 ^ 2 / 32 - mu2 * mu4 / 8) -
        (3 * mu3p ^ 2 / 32 - mu2p * mu4p / 8)) = 0 := by
    have hcf_raw :
        f2 * (3 * mu3 ^ 2 / 32 - mu2 * mu4 / 8) - f3 * mu2 ^ 3 / 64 =
          f2 * (3 * mu3p ^ 2 / 32 - mu2p * mu4p / 8) -
            f3 * mu2p ^ 3 / 64 := by
      rw [← hCf, ← hCfp]
      exact hCfEq
    have hcf_raw' :
        f2 * (3 * mu3 ^ 2 / 32 - mu2 * mu4 / 8) - f3 * mu2 ^ 3 / 64 =
          f2 * (3 * mu3p ^ 2 / 32 - mu2p * mu4p / 8) - f3 * mu2 ^ 3 / 64 := by
      simpa [hmu2p_pow] using hcf_raw
    calc
      f2 * ((3 * mu3 ^ 2 / 32 - mu2 * mu4 / 8) -
          (3 * mu3p ^ 2 / 32 - mu2p * mu4p / 8))
          = (f2 * (3 * mu3 ^ 2 / 32 - mu2 * mu4 / 8) - f3 * mu2 ^ 3 / 64) -
              (f2 * (3 * mu3p ^ 2 / 32 - mu2p * mu4p / 8) -
                f3 * mu2 ^ 3 / 64) := by ring
      _ = 0 := by rw [hcf_raw']; ring
  have hg_system :
      g2 * ((3 * mu3 ^ 2 / 32 - mu2 * mu4 / 8) -
        (3 * mu3p ^ 2 / 32 - mu2p * mu4p / 8)) = 0 := by
    have hcg_raw :
        g2 * (3 * mu3 ^ 2 / 32 - mu2 * mu4 / 8) - g3 * mu2 ^ 3 / 64 =
          g2 * (3 * mu3p ^ 2 / 32 - mu2p * mu4p / 8) -
            g3 * mu2p ^ 3 / 64 := by
      rw [← hCg, ← hCgp]
      exact hCgEq
    have hcg_raw' :
        g2 * (3 * mu3 ^ 2 / 32 - mu2 * mu4 / 8) - g3 * mu2 ^ 3 / 64 =
          g2 * (3 * mu3p ^ 2 / 32 - mu2p * mu4p / 8) - g3 * mu2 ^ 3 / 64 := by
      simpa [hmu2p_pow] using hcg_raw
    calc
      g2 * ((3 * mu3 ^ 2 / 32 - mu2 * mu4 / 8) -
          (3 * mu3p ^ 2 / 32 - mu2p * mu4p / 8))
          = (g2 * (3 * mu3 ^ 2 / 32 - mu2 * mu4 / 8) - g3 * mu2 ^ 3 / 64) -
              (g2 * (3 * mu3p ^ 2 / 32 - mu2p * mu4p / 8) -
                g3 * mu2 ^ 3 / 64) := by ring
      _ = 0 := by rw [hcg_raw']; ring
  have hfg_nonzero : f2 ≠ 0 ∨ g2 ≠ 0 := by
    by_contra hzero
    push_neg at hzero
    exact hdet (by rw [hzero.1, hzero.2]; ring)
  have hlinear :
      (3 * mu3 ^ 2 / 32 - mu2 * mu4 / 8) =
        (3 * mu3p ^ 2 / 32 - mu2p * mu4p / 8) := by
    have hzero :
        (3 * mu3 ^ 2 / 32 - mu2 * mu4 / 8) -
          (3 * mu3p ^ 2 / 32 - mu2p * mu4p / 8) = 0 := by
      cases hfg_nonzero with
      | inl hf =>
          exact mul_eq_zero.mp hf_system |>.resolve_left hf
      | inr hg =>
          exact mul_eq_zero.mp hg_system |>.resolve_left hg
    linarith
  have hmu4_eq : mu4 = mu4p := by
    have hlinear' :
        (3 * mu3 ^ 2 / 32 - mu2 * mu4 / 8) =
          (3 * mu3 ^ 2 / 32 - mu2 * mu4p / 8) := by
      simpa [← hmu2_eq, ← hmu3_sq_eq] using hlinear
    have hmul : mu2 * mu4 = mu2 * mu4p := by
      nlinarith [hlinear']
    exact mul_left_cancel₀ hmu2_ne hmul
  exact ⟨hmu2_eq, habs_mu3, hmu4_eq⟩

end Omega.Conclusion
