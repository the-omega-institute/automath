import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

noncomputable section

/-- Order-`2` Rényi entropy written from the collision probability. -/
def conclusion_renyi2_effective_support_zero_density_collapse_H2
    (Col : ℕ → ℝ) (m : ℕ) : ℝ :=
  -Real.log (Col m)

/-- Order-`2` effective support written from the collision probability. -/
def conclusion_renyi2_effective_support_zero_density_collapse_Neff2
    (Col : ℕ → ℝ) (m : ℕ) : ℝ :=
  1 / Col m

/-- The logarithmic density gap `H₂ - log M`. -/
def conclusion_renyi2_effective_support_zero_density_collapse_entropyGap
    (M Col : ℕ → ℝ) (m : ℕ) : ℝ :=
  conclusion_renyi2_effective_support_zero_density_collapse_H2 Col m - Real.log (M m)

/-- The normalized order-`2` effective-support density. -/
def conclusion_renyi2_effective_support_zero_density_collapse_density
    (M Col : ℕ → ℝ) (m : ℕ) : ℝ :=
  conclusion_renyi2_effective_support_zero_density_collapse_Neff2 Col m / M m

/-- Eventual divergence of the normalized collision scale. -/
def conclusion_renyi2_effective_support_zero_density_collapse_collisionScaleDiverges
    (M Col : ℕ → ℝ) : Prop :=
  ∀ B : ℝ, ∃ N : ℕ, ∀ m ≥ N, B ≤ M m * Col m

/-- Paper label: `thm:conclusion-renyi2-effective-support-zero-density-collapse`. Unfolding
`H₂` and `N_eff^(2)` turns the two target limits into the reciprocal and logarithm of the
collision scale `M_m * Col_m`; once that scale diverges, the effective support has zero density
and the Rényi-`2` entropy stays a logarithmic distance `→ -∞` below the ambient support size. -/
theorem paper_conclusion_renyi2_effective_support_zero_density_collapse
    (M Col : ℕ → ℝ)
    (hMpos : ∀ m, 0 < M m)
    (hColpos : ∀ m, 0 < Col m)
    (hdiv :
      conclusion_renyi2_effective_support_zero_density_collapse_collisionScaleDiverges M Col) :
    (∀ m,
      conclusion_renyi2_effective_support_zero_density_collapse_entropyGap M Col m =
        -Real.log (M m * Col m)) ∧
      (∀ m,
        conclusion_renyi2_effective_support_zero_density_collapse_density M Col m =
          1 / (M m * Col m)) ∧
      (∀ R : ℝ, ∃ N : ℕ, ∀ m ≥ N,
        conclusion_renyi2_effective_support_zero_density_collapse_entropyGap M Col m ≤ R) ∧
      (∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N,
        |conclusion_renyi2_effective_support_zero_density_collapse_density M Col m| < ε) := by
  have hGap :
      ∀ m,
        conclusion_renyi2_effective_support_zero_density_collapse_entropyGap M Col m =
          -Real.log (M m * Col m) := by
    intro m
    unfold conclusion_renyi2_effective_support_zero_density_collapse_entropyGap
      conclusion_renyi2_effective_support_zero_density_collapse_H2
    have hlogmul : Real.log (M m * Col m) = Real.log (M m) + Real.log (Col m) := by
      rw [Real.log_mul (hMpos m).ne' (hColpos m).ne']
    linarith
  have hDensity :
      ∀ m,
        conclusion_renyi2_effective_support_zero_density_collapse_density M Col m =
          1 / (M m * Col m) := by
    intro m
    unfold conclusion_renyi2_effective_support_zero_density_collapse_density
      conclusion_renyi2_effective_support_zero_density_collapse_Neff2
    field_simp [(hMpos m).ne', (hColpos m).ne']
  refine ⟨hGap, hDensity, ?_, ?_⟩
  · intro R
    obtain ⟨N, hN⟩ := hdiv (Real.exp (-R))
    refine ⟨N, ?_⟩
    intro m hm
    have hscale : Real.exp (-R) ≤ M m * Col m := hN m hm
    have hscale_pos : 0 < M m * Col m := mul_pos (hMpos m) (hColpos m)
    have hlog : -R ≤ Real.log (M m * Col m) := by
      exact (Real.le_log_iff_exp_le hscale_pos).2 hscale
    rw [hGap m]
    linarith
  · intro ε hε
    obtain ⟨N, hN⟩ := hdiv (2 / ε)
    refine ⟨N, ?_⟩
    intro m hm
    have hscale : 2 / ε ≤ M m * Col m := hN m hm
    have hscale_pos : 0 < M m * Col m := mul_pos (hMpos m) (hColpos m)
    have hdensity_nonneg :
        0 ≤ conclusion_renyi2_effective_support_zero_density_collapse_density M Col m := by
      rw [hDensity m]
      positivity
    have hbound : 1 / (M m * Col m) ≤ ε / 2 := by
      have htwo_over_eps_pos : 0 < 2 / ε := by positivity
      calc
        1 / (M m * Col m) ≤ 1 / (2 / ε) :=
          one_div_le_one_div_of_le htwo_over_eps_pos hscale
        _ = ε / 2 := by
          field_simp [hε.ne']
    rw [abs_of_nonneg hdensity_nonneg, hDensity m]
    calc
      1 / (M m * Col m) ≤ ε / 2 := hbound
      _ < ε := by linarith

end

end Omega.Conclusion
