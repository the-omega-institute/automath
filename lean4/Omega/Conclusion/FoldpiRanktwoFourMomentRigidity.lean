import Mathlib.Tactic

namespace Omega.Conclusion

noncomputable section

/-- Paper label: `thm:conclusion-foldpi-ranktwo-four-moment-rigidity`.  A rank-two
second-order recurrence agreeing with the fold-π recurrence in the first four moments and with
nonzero Hankel determinant must have the same recurrence coefficients, hence the same tail. -/
theorem paper_conclusion_foldpi_ranktwo_four_moment_rigidity
    (φ : ℝ) (f g : ℕ → ℝ)
    (hrec_f :
      ∀ k, 1 ≤ k →
        f (k + 2) = (1 + φ ^ 2) * f (k + 1) - φ ^ 2 * f k)
    (hrec_g :
      ∃ A B : ℝ, ∀ k, 1 ≤ k → g (k + 2) = A * g (k + 1) + B * g k)
    (hdet : f 2 * f 2 - f 1 * f 3 ≠ 0)
    (h1 : g 1 = f 1) (h2 : g 2 = f 2) (h3 : g 3 = f 3) (h4 : g 4 = f 4) :
    ∀ k, 1 ≤ k → g k = f k := by
  rcases hrec_g with ⟨A, B, hrec_g⟩
  set a : ℝ := 1 + φ ^ 2
  set b : ℝ := -φ ^ 2
  have hf3 : f 3 = a * f 2 + b * f 1 := by
    have h := hrec_f 1 (by norm_num)
    dsimp [a, b]
    linarith
  have hf4 : f 4 = a * f 3 + b * f 2 := by
    have h := hrec_f 2 (by norm_num)
    dsimp [a, b]
    linarith
  have hg3 : g 3 = A * g 2 + B * g 1 := hrec_g 1 (by norm_num)
  have hg4 : g 4 = A * g 3 + B * g 2 := hrec_g 2 (by norm_num)
  have hlin1 : (A - a) * f 2 + (B - b) * f 1 = 0 := by
    rw [h1, h2, h3, hf3] at hg3
    linarith
  have hlin2 : (A - a) * f 3 + (B - b) * f 2 = 0 := by
    rw [h2, h3, h4, hf4] at hg4
    linarith
  have hA : A = a := by
    have hzero : (A - a) * (f 2 * f 2 - f 1 * f 3) = 0 := by
      calc
        (A - a) * (f 2 * f 2 - f 1 * f 3)
            = f 2 * ((A - a) * f 2 + (B - b) * f 1) -
                f 1 * ((A - a) * f 3 + (B - b) * f 2) := by ring
        _ = 0 := by rw [hlin1, hlin2]; ring
    have hzero' : (f 2 * f 2 - f 1 * f 3) * (A - a) = 0 := by
      simpa [mul_comm] using hzero
    exact sub_eq_zero.mp (eq_zero_of_ne_zero_of_mul_left_eq_zero hdet hzero')
  have hB : B = b := by
    have hzero : (B - b) * (f 1 * f 3 - f 2 * f 2) = 0 := by
      calc
        (B - b) * (f 1 * f 3 - f 2 * f 2)
            = f 3 * ((A - a) * f 2 + (B - b) * f 1) -
                f 2 * ((A - a) * f 3 + (B - b) * f 2) := by ring
        _ = 0 := by rw [hlin1, hlin2]; ring
    have hdet' : f 1 * f 3 - f 2 * f 2 ≠ 0 := by
      intro h
      apply hdet
      linarith
    have hzero' : (f 1 * f 3 - f 2 * f 2) * (B - b) = 0 := by
      simpa [mul_comm] using hzero
    exact sub_eq_zero.mp (eq_zero_of_ne_zero_of_mul_left_eq_zero hdet' hzero')
  have hrec_g' :
      ∀ k, 1 ≤ k → g (k + 2) = a * g (k + 1) + b * g k := by
    intro k hk
    rw [hrec_g k hk, hA, hB]
  have hrec_f' :
      ∀ k, 1 ≤ k → f (k + 2) = a * f (k + 1) + b * f k := by
    intro k hk
    have h := hrec_f k hk
    dsimp [a, b]
    linarith
  have htail : ∀ n, g (n + 1) = f (n + 1) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      rcases n with _ | n
      · simpa using h1
      rcases n with _ | n
      · simpa using h2
      have hprev : g ((n + 1) + 1) = f ((n + 1) + 1) := ih (n + 1) (by omega)
      have hprev' : g (n + 1) = f (n + 1) := ih n (by omega)
      have hg := hrec_g' (n + 1) (by omega)
      have hf := hrec_f' (n + 1) (by omega)
      rw [hprev, hprev'] at hg
      linarith
  intro k hk
  have hk' : k = (k - 1) + 1 := by omega
  rw [hk']
  exact htail (k - 1)

end

end Omega.Conclusion
