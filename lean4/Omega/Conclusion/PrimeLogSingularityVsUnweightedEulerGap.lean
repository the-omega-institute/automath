import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete logarithmic-derivative package comparing the prime-log boundary current with
finite-factor-removed unweighted Euler products and a nonvanishing holomorphic multiplier. -/
structure conclusion_prime_log_singularity_vs_unweighted_euler_gap_data where
  conclusion_prime_log_singularity_vs_unweighted_euler_gap_prime_log_boundary :
    ℝ → ℝ
  conclusion_prime_log_singularity_vs_unweighted_euler_gap_unweighted_log_derivative :
    ℝ → ℝ
  conclusion_prime_log_singularity_vs_unweighted_euler_gap_finite_factor_log_derivative :
    Finset ℕ → ℝ → ℝ
  conclusion_prime_log_singularity_vs_unweighted_euler_gap_multiplier_log_derivative :
    ℝ → ℝ
  conclusion_prime_log_singularity_vs_unweighted_euler_gap_regular_log_derivative :
    Finset ℕ → ℝ → ℝ
  conclusion_prime_log_singularity_vs_unweighted_euler_gap_regular_eq :
    ∀ F σ,
      conclusion_prime_log_singularity_vs_unweighted_euler_gap_regular_log_derivative F σ =
        conclusion_prime_log_singularity_vs_unweighted_euler_gap_unweighted_log_derivative σ +
          conclusion_prime_log_singularity_vs_unweighted_euler_gap_finite_factor_log_derivative F σ +
            conclusion_prime_log_singularity_vs_unweighted_euler_gap_multiplier_log_derivative σ
  conclusion_prime_log_singularity_vs_unweighted_euler_gap_prime_log_unbounded :
    ∀ C ε : ℝ,
      0 < ε →
        ∃ σ,
          1 < σ ∧
            σ < 1 + ε ∧
              C <
                |conclusion_prime_log_singularity_vs_unweighted_euler_gap_prime_log_boundary σ|
  conclusion_prime_log_singularity_vs_unweighted_euler_gap_unweighted_bounded :
    ∃ C ε : ℝ,
      0 < ε ∧
        ∀ σ,
          1 < σ →
            σ < 1 + ε →
              |conclusion_prime_log_singularity_vs_unweighted_euler_gap_unweighted_log_derivative
                σ| ≤ C
  conclusion_prime_log_singularity_vs_unweighted_euler_gap_finite_factor_bounded :
    ∀ F,
      ∃ C ε : ℝ,
        0 < ε ∧
          ∀ σ,
            1 < σ →
              σ < 1 + ε →
                |conclusion_prime_log_singularity_vs_unweighted_euler_gap_finite_factor_log_derivative
                  F σ| ≤ C
  conclusion_prime_log_singularity_vs_unweighted_euler_gap_multiplier_bounded :
    ∃ C ε : ℝ,
      0 < ε ∧
        ∀ σ,
          1 < σ →
            σ < 1 + ε →
              |conclusion_prime_log_singularity_vs_unweighted_euler_gap_multiplier_log_derivative
                σ| ≤ C

/-- The two boundary functions would have the same singularity class if their difference were
bounded in a punctured right-neighborhood of `1`. -/
def conclusion_prime_log_singularity_vs_unweighted_euler_gap_same_singularity
    (D : conclusion_prime_log_singularity_vs_unweighted_euler_gap_data) (F : Finset ℕ) : Prop :=
  ∃ C ε : ℝ,
    0 < ε ∧
      ∀ σ,
        1 < σ →
          σ < 1 + ε →
            |D.conclusion_prime_log_singularity_vs_unweighted_euler_gap_prime_log_boundary σ -
              D.conclusion_prime_log_singularity_vs_unweighted_euler_gap_regular_log_derivative
                F σ| ≤ C

/-- No finite Euler-factor removal and nonvanishing holomorphic multiplier can reproduce the
prime-log logarithmic singularity class. -/
def conclusion_prime_log_singularity_vs_unweighted_euler_gap_statement
    (D : conclusion_prime_log_singularity_vs_unweighted_euler_gap_data) : Prop :=
  ∀ F,
    ¬ conclusion_prime_log_singularity_vs_unweighted_euler_gap_same_singularity D F

/-- Paper label: `thm:conclusion-prime-log-singularity-vs-unweighted-euler-gap`. -/
theorem paper_conclusion_prime_log_singularity_vs_unweighted_euler_gap
    (D : conclusion_prime_log_singularity_vs_unweighted_euler_gap_data) :
    conclusion_prime_log_singularity_vs_unweighted_euler_gap_statement D := by
  intro F hsame
  obtain ⟨Cdiff, εdiff, hεdiff, hdiff⟩ := hsame
  obtain ⟨Cu, εu, hεu, hu⟩ :=
    D.conclusion_prime_log_singularity_vs_unweighted_euler_gap_unweighted_bounded
  obtain ⟨Cf, εf, hεf, hf⟩ :=
    D.conclusion_prime_log_singularity_vs_unweighted_euler_gap_finite_factor_bounded F
  obtain ⟨Cm, εm, hεm, hm⟩ :=
    D.conclusion_prime_log_singularity_vs_unweighted_euler_gap_multiplier_bounded
  let ε := min εdiff (min εu (min εf εm))
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  let Cregular := Cu + Cf + Cm
  obtain ⟨σ, hσ1, hσε, hlarge⟩ :=
    D.conclusion_prime_log_singularity_vs_unweighted_euler_gap_prime_log_unbounded
      (Cdiff + Cregular + 1) ε hε
  have hσdiff : σ < 1 + εdiff := by
    dsimp [ε] at hσε
    nlinarith [min_le_left εdiff (min εu (min εf εm))]
  have hσu : σ < 1 + εu := by
    dsimp [ε] at hσε
    nlinarith [min_le_left εu (min εf εm),
      min_le_right εdiff (min εu (min εf εm))]
  have hσf : σ < 1 + εf := by
    dsimp [ε] at hσε
    nlinarith [min_le_left εf εm, min_le_right εu (min εf εm),
      min_le_right εdiff (min εu (min εf εm))]
  have hσm : σ < 1 + εm := by
    dsimp [ε] at hσε
    nlinarith [min_le_right εf εm, min_le_right εu (min εf εm),
      min_le_right εdiff (min εu (min εf εm))]
  have hregular : |D.conclusion_prime_log_singularity_vs_unweighted_euler_gap_regular_log_derivative
      F σ| ≤ Cregular := by
    rw [D.conclusion_prime_log_singularity_vs_unweighted_euler_gap_regular_eq F σ]
    have huσ := hu σ hσ1 hσu
    have hfσ := hf σ hσ1 hσf
    have hmσ := hm σ hσ1 hσm
    calc
      |D.conclusion_prime_log_singularity_vs_unweighted_euler_gap_unweighted_log_derivative σ +
          D.conclusion_prime_log_singularity_vs_unweighted_euler_gap_finite_factor_log_derivative
            F σ +
            D.conclusion_prime_log_singularity_vs_unweighted_euler_gap_multiplier_log_derivative
              σ| ≤
          |D.conclusion_prime_log_singularity_vs_unweighted_euler_gap_unweighted_log_derivative
              σ| +
            |D.conclusion_prime_log_singularity_vs_unweighted_euler_gap_finite_factor_log_derivative
              F σ| +
              |D.conclusion_prime_log_singularity_vs_unweighted_euler_gap_multiplier_log_derivative
                σ| := by
          calc
            |D.conclusion_prime_log_singularity_vs_unweighted_euler_gap_unweighted_log_derivative
                σ +
                D.conclusion_prime_log_singularity_vs_unweighted_euler_gap_finite_factor_log_derivative
                  F σ +
                  D.conclusion_prime_log_singularity_vs_unweighted_euler_gap_multiplier_log_derivative
                    σ| ≤
                |D.conclusion_prime_log_singularity_vs_unweighted_euler_gap_unweighted_log_derivative
                  σ +
                  D.conclusion_prime_log_singularity_vs_unweighted_euler_gap_finite_factor_log_derivative
                    F σ| +
                  |D.conclusion_prime_log_singularity_vs_unweighted_euler_gap_multiplier_log_derivative
                    σ| := abs_add_le _ _
            _ ≤
                |D.conclusion_prime_log_singularity_vs_unweighted_euler_gap_unweighted_log_derivative
                  σ| +
                  |D.conclusion_prime_log_singularity_vs_unweighted_euler_gap_finite_factor_log_derivative
                    F σ| +
                    |D.conclusion_prime_log_singularity_vs_unweighted_euler_gap_multiplier_log_derivative
                      σ| := by
              nlinarith [abs_add_le
                (D.conclusion_prime_log_singularity_vs_unweighted_euler_gap_unweighted_log_derivative
                  σ)
                (D.conclusion_prime_log_singularity_vs_unweighted_euler_gap_finite_factor_log_derivative
                  F σ)]
      _ ≤ Cregular := by
        dsimp [Cregular]
        nlinarith
  have hprime_bound :
      |D.conclusion_prime_log_singularity_vs_unweighted_euler_gap_prime_log_boundary σ| ≤
        Cdiff + Cregular := by
    have hdiffσ := hdiff σ hσ1 hσdiff
    calc
      |D.conclusion_prime_log_singularity_vs_unweighted_euler_gap_prime_log_boundary σ| =
          |(D.conclusion_prime_log_singularity_vs_unweighted_euler_gap_prime_log_boundary σ -
              D.conclusion_prime_log_singularity_vs_unweighted_euler_gap_regular_log_derivative
                F σ) +
              D.conclusion_prime_log_singularity_vs_unweighted_euler_gap_regular_log_derivative
                F σ| := by ring_nf
      _ ≤
          |D.conclusion_prime_log_singularity_vs_unweighted_euler_gap_prime_log_boundary σ -
            D.conclusion_prime_log_singularity_vs_unweighted_euler_gap_regular_log_derivative
              F σ| +
            |D.conclusion_prime_log_singularity_vs_unweighted_euler_gap_regular_log_derivative
              F σ| := abs_add_le _ _
      _ ≤ Cdiff + Cregular := by
        nlinarith
  nlinarith

end Omega.Conclusion
