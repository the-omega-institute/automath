import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

noncomputable section

/-- Concrete automatic-Dirichlet moment data.  The `momentValue` is bounded by diagonal and
off-diagonal pieces; the supplied spectral-gap and near-diagonal certificates bound both pieces by
the same power-saving scale. -/
structure gm_automatic_dirichlet_moment_bound_data where
  gm_automatic_dirichlet_moment_bound_N : ℕ
  gm_automatic_dirichlet_moment_bound_logExponent : ℕ → ℕ
  gm_automatic_dirichlet_moment_bound_momentValue : ℕ → ℝ → ℝ
  gm_automatic_dirichlet_moment_bound_diagonalContribution : ℕ → ℝ → ℝ
  gm_automatic_dirichlet_moment_bound_offDiagonalContribution : ℕ → ℝ → ℝ
  gm_automatic_dirichlet_moment_bound_saving : ℕ → ℝ
  gm_automatic_dirichlet_moment_bound_diagonalConstant : ℕ → ℝ
  gm_automatic_dirichlet_moment_bound_offDiagonalConstant : ℕ → ℝ
  gm_automatic_dirichlet_moment_bound_saving_pos :
    ∀ k : ℕ, 0 < gm_automatic_dirichlet_moment_bound_saving k
  gm_automatic_dirichlet_moment_bound_diagonalConstant_pos :
    ∀ k : ℕ, 0 < gm_automatic_dirichlet_moment_bound_diagonalConstant k
  gm_automatic_dirichlet_moment_bound_offDiagonalConstant_pos :
    ∀ k : ℕ, 0 < gm_automatic_dirichlet_moment_bound_offDiagonalConstant k
  gm_automatic_dirichlet_moment_bound_expansion :
    ∀ k : ℕ, ∀ T : ℝ, 1 ≤ T →
      gm_automatic_dirichlet_moment_bound_momentValue k T ≤
        gm_automatic_dirichlet_moment_bound_diagonalContribution k T +
          gm_automatic_dirichlet_moment_bound_offDiagonalContribution k T
  gm_automatic_dirichlet_moment_bound_diagonal_bound :
    ∀ k : ℕ, ∀ T : ℝ, 1 ≤ T →
      gm_automatic_dirichlet_moment_bound_diagonalContribution k T ≤
        gm_automatic_dirichlet_moment_bound_diagonalConstant k * T *
          (gm_automatic_dirichlet_moment_bound_N : ℝ) ^ k *
            (Real.log (gm_automatic_dirichlet_moment_bound_N : ℝ)) ^
              (gm_automatic_dirichlet_moment_bound_logExponent k) *
              (gm_automatic_dirichlet_moment_bound_N : ℝ) ^
                (-(gm_automatic_dirichlet_moment_bound_saving k))
  gm_automatic_dirichlet_moment_bound_offDiagonal_bound :
    ∀ k : ℕ, ∀ T : ℝ, 1 ≤ T →
      gm_automatic_dirichlet_moment_bound_offDiagonalContribution k T ≤
        gm_automatic_dirichlet_moment_bound_offDiagonalConstant k * T *
          (gm_automatic_dirichlet_moment_bound_N : ℝ) ^ k *
            (Real.log (gm_automatic_dirichlet_moment_bound_N : ℝ)) ^
              (gm_automatic_dirichlet_moment_bound_logExponent k) *
              (gm_automatic_dirichlet_moment_bound_N : ℝ) ^
                (-(gm_automatic_dirichlet_moment_bound_saving k))

namespace gm_automatic_dirichlet_moment_bound_data

/-- The common scale appearing after the diagonal/off-diagonal expansion. -/
def gm_automatic_dirichlet_moment_bound_scale
    (D : gm_automatic_dirichlet_moment_bound_data) (k : ℕ) (T : ℝ) : ℝ :=
  T * (D.gm_automatic_dirichlet_moment_bound_N : ℝ) ^ k *
    (Real.log (D.gm_automatic_dirichlet_moment_bound_N : ℝ)) ^
      (D.gm_automatic_dirichlet_moment_bound_logExponent k) *
      (D.gm_automatic_dirichlet_moment_bound_N : ℝ) ^
        (-(D.gm_automatic_dirichlet_moment_bound_saving k))

/-- Paper-facing moment bound: every fixed `2k`-th moment has a positive power saving with an
explicit constant. -/
def moment_bound (D : gm_automatic_dirichlet_moment_bound_data) : Prop :=
  ∀ k : ℕ,
    ∃ ε C : ℝ,
      0 < ε ∧
        0 < C ∧
          ∀ T : ℝ, 1 ≤ T →
            D.gm_automatic_dirichlet_moment_bound_momentValue k T ≤
              C * D.gm_automatic_dirichlet_moment_bound_scale k T

end gm_automatic_dirichlet_moment_bound_data

open gm_automatic_dirichlet_moment_bound_data

/-- Paper label: `thm:gm-automatic-dirichlet-moment-bound`. -/
theorem paper_gm_automatic_dirichlet_moment_bound
    (D : gm_automatic_dirichlet_moment_bound_data) : D.moment_bound := by
  intro k
  refine ⟨D.gm_automatic_dirichlet_moment_bound_saving k,
    D.gm_automatic_dirichlet_moment_bound_diagonalConstant k +
      D.gm_automatic_dirichlet_moment_bound_offDiagonalConstant k,
    D.gm_automatic_dirichlet_moment_bound_saving_pos k, ?_, ?_⟩
  · linarith [D.gm_automatic_dirichlet_moment_bound_diagonalConstant_pos k,
      D.gm_automatic_dirichlet_moment_bound_offDiagonalConstant_pos k]
  · intro T hT
    have hExpansion :=
      D.gm_automatic_dirichlet_moment_bound_expansion k T hT
    have hDiagonal :=
      D.gm_automatic_dirichlet_moment_bound_diagonal_bound k T hT
    have hOffDiagonal :=
      D.gm_automatic_dirichlet_moment_bound_offDiagonal_bound k T hT
    calc
      D.gm_automatic_dirichlet_moment_bound_momentValue k T
          ≤ D.gm_automatic_dirichlet_moment_bound_diagonalContribution k T +
              D.gm_automatic_dirichlet_moment_bound_offDiagonalContribution k T := hExpansion
      _ ≤ D.gm_automatic_dirichlet_moment_bound_diagonalConstant k *
              D.gm_automatic_dirichlet_moment_bound_scale k T +
            D.gm_automatic_dirichlet_moment_bound_offDiagonalConstant k *
              D.gm_automatic_dirichlet_moment_bound_scale k T := by
          simpa [gm_automatic_dirichlet_moment_bound_scale, mul_assoc] using
            add_le_add hDiagonal hOffDiagonal
      _ = (D.gm_automatic_dirichlet_moment_bound_diagonalConstant k +
              D.gm_automatic_dirichlet_moment_bound_offDiagonalConstant k) *
            D.gm_automatic_dirichlet_moment_bound_scale k T := by
          ring

end

end Omega.SyncKernelWeighted
