import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Omega.SyncKernelWeighted.RealInput40PrimedirichletDenseBranch

namespace Omega.SyncKernelWeighted

noncomputable section

/-- The chapter-local analytic remainder after isolating the distinguished `k = p` branch. -/
def primedirichlet_branch_inherit_remainder (p : ℕ) : ℝ → ℝ :=
  fun σ => σ + Real.log (p : ℝ)

/-- Rescaled branch points for the inherited `k = p` contribution. -/
def primedirichlet_branch_inherit_scaled_point (p n : ℕ) (y : ℝ) : ℂ :=
  ⟨(p : ℝ) / (n + 1), y⟩

/-- The primitive-Dirichlet dense-branch package persists after isolating a fixed positive
`k = p` branch: the original dense-branch theorem still holds, the remainder is analytic, and the
rescaled branch points still approach the imaginary axis above a dense set of heights. -/
def primedirichlet_branch_inherit_statement : Prop :=
  RealInput40PrimedirichletDenseBranch ∧
    ∀ p : ℕ, 0 < p →
      AnalyticAt ℝ (primedirichlet_branch_inherit_remainder p) 0 ∧
        ∀ t ε : ℝ, 0 < ε →
          ∃ n : ℕ, ∃ y : ℝ, y ∈ realInput40DenseBranchHeights ∧
            |(primedirichlet_branch_inherit_scaled_point p n y).re| < ε ∧
            |(primedirichlet_branch_inherit_scaled_point p n y).im - t| < ε

private theorem primedirichlet_branch_inherit_scaled_point_re (p n : ℕ) (y : ℝ) :
    (primedirichlet_branch_inherit_scaled_point p n y).re = (p : ℝ) / (n + 1) := by
  rfl

private theorem primedirichlet_branch_inherit_scaled_point_im (p n : ℕ) (y : ℝ) :
    (primedirichlet_branch_inherit_scaled_point p n y).im = y := by
  rfl

/-- Paper label: `prop:primedirichlet-branch-inherit`. -/
theorem paper_primedirichlet_branch_inherit : primedirichlet_branch_inherit_statement := by
  rcases paper_real_input_40_primedirichlet_dense_branch with ⟨hsum, hDense, hNearAxis⟩
  refine ⟨⟨hsum, hDense, hNearAxis⟩, ?_⟩
  intro p hp
  refine ⟨?_, ?_⟩
  · simpa [primedirichlet_branch_inherit_remainder] using
      (analyticAt_id.add analyticAt_const :
        AnalyticAt ℝ (fun σ : ℝ => σ + Real.log (p : ℝ)) 0)
  · intro t ε hε
    have htClosure : t ∈ closure realInput40DenseBranchHeights := hDense t
    rcases Metric.mem_closure_iff.1 htClosure ε hε with ⟨y, hy, hyε⟩
    have hp_real : 0 < (p : ℝ) := by
      exact_mod_cast hp
    have hε_div : 0 < ε / (p : ℝ) := by
      exact div_pos hε hp_real
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε_div
    refine ⟨n, y, hy, ?_, ?_⟩
    · rw [primedirichlet_branch_inherit_scaled_point_re]
      have hn' : (((n : ℝ) + 1) : ℝ)⁻¹ < ε / (p : ℝ) := by
        simpa [one_div] using hn
      have hmul : (p : ℝ) * (((n : ℝ) + 1)⁻¹) < (p : ℝ) * (ε / (p : ℝ)) :=
        mul_lt_mul_of_pos_left hn' hp_real
      have hp_ne : (p : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt hp)
      have hscaled : (p : ℝ) * (((n : ℝ) + 1)⁻¹) < ε := by
        calc
          (p : ℝ) * (((n : ℝ) + 1)⁻¹) < (p : ℝ) * (ε / (p : ℝ)) := hmul
          _ = ε := by field_simp [hp_ne]
      have habs :
          |(p : ℝ) * (((n : ℝ) + 1)⁻¹)| = (p : ℝ) * (((n : ℝ) + 1)⁻¹) := by
        apply abs_of_nonneg
        positivity
      simpa [div_eq_mul_inv, habs] using hscaled
    · rw [primedirichlet_branch_inherit_scaled_point_im]
      simpa [abs_sub_comm, Real.dist_eq] using hyε

end

end Omega.SyncKernelWeighted
