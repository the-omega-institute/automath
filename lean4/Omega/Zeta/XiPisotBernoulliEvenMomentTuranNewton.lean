import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-pisot-bernoulli-even-moment-turan-newton`. -/
theorem paper_xi_pisot_bernoulli_even_moment_turan_newton (m γ : ℕ → ℝ)
    (hγ : ∀ r, γ r = Real.pi ^ (2 * r) / ((Nat.factorial (2 * r) : ℝ)) * m r)
    (hlogconc : ∀ r, 1 ≤ r → γ r ^ 2 > γ (r - 1) * γ (r + 1)) :
    ∀ r, 1 ≤ r →
      m r ^ 2 >
        ((((2 : ℝ) * (r : ℝ)) * (((2 : ℝ) * (r : ℝ)) - 1)) /
            ((((2 : ℝ) * (r : ℝ)) + 1) * (((2 : ℝ) * (r : ℝ)) + 2))) *
          m (r - 1) * m (r + 1) := by
  intro r hr
  let a : ℕ → ℝ := fun n => Real.pi ^ (2 * n) / ((Nat.factorial (2 * n) : ℝ))
  have ha_pos : ∀ n, 0 < a n := by
    intro n
    dsimp [a]
    positivity
  have hstrict :
      (a (r - 1) * m (r - 1)) * (a (r + 1) * m (r + 1)) <
        (a r * m r) ^ 2 := by
    have hbase := hlogconc r hr
    rw [hγ r, hγ (r - 1), hγ (r + 1)] at hbase
    simpa [a] using hbase
  have hscaled :
      (a (r - 1) * a (r + 1) / a r ^ 2) * m (r - 1) * m (r + 1) <
        m r ^ 2 := by
    have hdiv :=
      div_lt_div_of_pos_right hstrict (sq_pos_of_pos (ha_pos r))
    have hrhs : (a r * m r) ^ 2 / a r ^ 2 = m r ^ 2 := by
      field_simp [(ha_pos r).ne']
    have hlhs :
        ((a (r - 1) * m (r - 1)) * (a (r + 1) * m (r + 1))) / a r ^ 2 =
          (a (r - 1) * a (r + 1) / a r ^ 2) * m (r - 1) * m (r + 1) := by
      ring
    simpa [hlhs, hrhs] using hdiv
  have hcoeff :
      a (r - 1) * a (r + 1) / a r ^ 2 =
        (((2 : ℝ) * (r : ℝ)) * (((2 : ℝ) * (r : ℝ)) - 1)) /
          ((((2 : ℝ) * (r : ℝ)) + 1) * (((2 : ℝ) * (r : ℝ)) + 2)) := by
    cases r with
    | zero =>
        norm_num at hr
    | succ s =>
        have hfac2_nat :
            Nat.factorial (2 + s * 2) =
              (2 + s * 2) * ((1 + s * 2) * Nat.factorial (s * 2)) := by
          rw [show 2 + s * 2 = (1 + s * 2) + 1 by omega, Nat.factorial_succ]
          rw [show 1 + s * 2 = s * 2 + 1 by omega, Nat.factorial_succ]
        have hfac4_nat :
            Nat.factorial (4 + s * 2) =
              (4 + s * 2) *
                ((3 + s * 2) *
                  ((2 + s * 2) * ((1 + s * 2) * Nat.factorial (s * 2)))) := by
          rw [show 4 + s * 2 = (3 + s * 2) + 1 by omega, Nat.factorial_succ]
          rw [show 3 + s * 2 = (2 + s * 2) + 1 by omega, Nat.factorial_succ]
          rw [show 2 + s * 2 = (1 + s * 2) + 1 by omega, Nat.factorial_succ]
          rw [show 1 + s * 2 = s * 2 + 1 by omega, Nat.factorial_succ]
        have hfac2 :
            (Nat.factorial (2 + s * 2) : ℝ) =
              ((2 + s * 2 : ℕ) : ℝ) *
                (((1 + s * 2 : ℕ) : ℝ) * (Nat.factorial (s * 2) : ℝ)) := by
          exact_mod_cast hfac2_nat
        have hfac4 :
            (Nat.factorial (4 + s * 2) : ℝ) =
              ((4 + s * 2 : ℕ) : ℝ) *
                (((3 + s * 2 : ℕ) : ℝ) *
                  (((2 + s * 2 : ℕ) : ℝ) *
                    (((1 + s * 2 : ℕ) : ℝ) * (Nat.factorial (s * 2) : ℝ)))) := by
          exact_mod_cast hfac4_nat
        have hfac_ne : (Nat.factorial (s * 2) : ℝ) ≠ 0 := by positivity
        have h1 : ((1 + s * 2 : ℕ) : ℝ) ≠ 0 := by positivity
        have h2 : ((2 + s * 2 : ℕ) : ℝ) ≠ 0 := by positivity
        have h3 : ((3 + s * 2 : ℕ) : ℝ) ≠ 0 := by positivity
        have h4 : ((4 + s * 2 : ℕ) : ℝ) ≠ 0 := by positivity
        dsimp [a]
        rw [show 2 * s = s * 2 by omega]
        rw [show 2 * (s + 1) = 2 + s * 2 by omega]
        rw [show 2 * (s + 1 + 1) = 4 + s * 2 by omega]
        rw [hfac2, hfac4]
        field_simp [Real.pi_ne_zero, hfac_ne, h1, h2, h3, h4]
        norm_num [Nat.cast_add, Nat.cast_mul]
        ring_nf
  simpa [hcoeff] using hscaled

end Omega.Zeta
