import Mathlib

open Filter
open scoped Topology

/-- A fixed polynomial in `q` is eventually dominated by `exp (ε q)`. -/
lemma conclusion_moment_hankel_rank_polynomial_taming_pow_eventually_exp
    (N k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q →
      ((N + 1 : ℝ) ^ k) * (q : ℝ) ^ k ≤ Real.exp (ε * q) := by
  have hlittle :
      (fun x : ℝ => ((N + 1 : ℝ) ^ k) * x ^ k) =o[atTop]
        fun x : ℝ => Real.exp (ε * x) :=
    (isLittleO_pow_exp_pos_mul_atTop k hε).const_mul_left ((N + 1 : ℝ) ^ k)
  have hevent :
      ∀ᶠ x : ℝ in atTop,
        ‖((N + 1 : ℝ) ^ k) * x ^ k‖ ≤ (1 : ℝ) * ‖Real.exp (ε * x)‖ :=
    hlittle.bound zero_lt_one
  rw [eventually_atTop] at hevent
  obtain ⟨R, hR⟩ := hevent
  refine ⟨max 1 (⌈R⌉₊), fun q hq => ?_⟩
  have hqceil : ⌈R⌉₊ ≤ q := le_trans (Nat.le_max_right 1 ⌈R⌉₊) hq
  have hRq : R ≤ (q : ℝ) := (Nat.le_ceil R).trans (Nat.cast_le.mpr hqceil)
  have h := hR (q : ℝ) hRq
  have hnonneg : 0 ≤ ((N + 1 : ℝ) ^ k) * (q : ℝ) ^ k :=
    mul_nonneg (pow_nonneg (by positivity) _) (pow_nonneg (Nat.cast_nonneg q) _)
  have hexpnonneg : 0 ≤ Real.exp (ε * q) := (Real.exp_pos _).le
  have hNabs : |(N + 1 : ℝ)| = (N + 1 : ℝ) := abs_of_nonneg (by positivity)
  simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg, abs_of_nonneg hexpnonneg, hNabs] using h

/-- Paper label: `thm:conclusion-moment-hankel-rank-polynomial-taming`. -/
theorem paper_conclusion_moment_hankel_rank_polynomial_taming
    (N : ℕ) (d : ℕ → ℕ)
    (hbound : ∀ q, 2 ≤ q → d q ≤ Nat.choose (q + N - 1) (N - 1)) :
    (∀ q, 2 ≤ q → d q ≤ Nat.choose (q + N - 1) (N - 1)) ∧
      (∀ ε : ℝ, 0 < ε → ∃ Q, ∀ q, Q ≤ q → (d q : ℝ) ≤ Real.exp (ε * q)) := by
  refine ⟨hbound, ?_⟩
  intro ε hε
  obtain ⟨Q₀, hQ₀⟩ :=
    conclusion_moment_hankel_rank_polynomial_taming_pow_eventually_exp N (N - 1) hε
  refine ⟨max 2 Q₀, fun q hq => ?_⟩
  have hq2 : 2 ≤ q := le_trans (Nat.le_max_left 2 Q₀) hq
  have hq1 : 1 ≤ q := by omega
  have hqQ₀ : Q₀ ≤ q := le_trans (Nat.le_max_right 2 Q₀) hq
  have hNle : N ≤ N * q := Nat.le_mul_of_pos_right N (Nat.succ_le_iff.mp hq1)
  have htop : q + N ≤ (N + 1) * q := by
    calc
      q + N = N + q := by omega
      _ ≤ N * q + q := Nat.add_le_add_right hNle q
      _ = (N + 1) * q := by rw [Nat.add_one, Nat.succ_mul]
  have harg : q + N - 1 ≤ (N + 1) * q := (Nat.sub_le _ _).trans htop
  have hchooseNat :
      Nat.choose (q + N - 1) (N - 1) ≤ ((N + 1) * q) ^ (N - 1) :=
    (Nat.choose_le_pow (q + N - 1) (N - 1)).trans (Nat.pow_le_pow_left harg _)
  have hdchoose : (d q : ℝ) ≤ (Nat.choose (q + N - 1) (N - 1) : ℝ) := by
    exact_mod_cast hbound q hq2
  have hchoosepow :
      (Nat.choose (q + N - 1) (N - 1) : ℝ) ≤
        ((N + 1 : ℝ) ^ (N - 1)) * (q : ℝ) ^ (N - 1) := by
    calc
      (Nat.choose (q + N - 1) (N - 1) : ℝ) ≤
          (((N + 1) * q) ^ (N - 1) : ℕ) := by exact_mod_cast hchooseNat
      _ = ((N + 1 : ℝ) * (q : ℝ)) ^ (N - 1) := by norm_num
      _ = ((N + 1 : ℝ) ^ (N - 1)) * (q : ℝ) ^ (N - 1) := by rw [mul_pow]
  exact hdchoose.trans (hchoosepow.trans (hQ₀ q hqQ₀))
