import Mathlib
import Omega.Conclusion.LkFixedIndexHardEdge
import Omega.POM.LkSpectralZetaDirichlet

open Filter

namespace Omega.Conclusion

noncomputable section

/-- The normalized finite `L_k` spectral zeta sum. -/
def conclusion_lk_normalized_zeta_odd_projector_normalized_zeta (k : ℕ) (s : ℝ) : ℝ :=
  (Real.pi / (2 * k + 1 : ℝ)) ^ (2 * s) * Omega.POM.pom_lk_spectral_zeta_dirichlet_spectral_zeta k s

/-- The finite odd-projector Dirichlet cutoff obtained by removing the even modes. -/
def conclusion_lk_normalized_zeta_odd_projector_odd_projector (k : ℕ) (s : ℝ) : ℝ :=
  Omega.POM.pom_lk_spectral_zeta_dirichlet_full_sum k s -
    Omega.POM.pom_lk_spectral_zeta_dirichlet_even_sum k s

/-- Concrete paper-facing package for the normalized `L_k` zeta and the odd-projector factor. -/
def conclusion_lk_normalized_zeta_odd_projector_statement : Prop :=
  (∀ k : ℕ, ∀ s : ℝ,
      conclusion_lk_normalized_zeta_odd_projector_normalized_zeta k s =
        (Real.pi / (2 * k + 1 : ℝ)) ^ (2 * s) *
          ∑ p : Fin k, (Omega.POM.lkEigenvalue k p) ^ (-s)) ∧
    (∀ k : ℕ, ∀ s : ℝ,
      conclusion_lk_normalized_zeta_odd_projector_odd_projector k s =
        (1 - (2 : ℝ) ^ (-2 * s)) * Omega.POM.pom_lk_spectral_zeta_dirichlet_full_sum k s) ∧
      (∀ k : ℕ, ∀ s : ℝ,
        (Real.pi / (2 * k + 1 : ℝ)) ^ (2 * s) *
            Omega.POM.pom_lk_spectral_zeta_dirichlet_proxy k s =
          Omega.POM.pom_lk_spectral_zeta_dirichlet_odd_sum k s) ∧
        ∀ p : ℕ,
          Tendsto
              (fun k : ℕ =>
                ((2 * k + 1 : ℝ) ^ 2) *
                  conclusion_lk_fixed_index_hard_edge_eigenvalue k p)
              atTop (nhds (((2 * p - 1 : ℝ) ^ 2) * Real.pi ^ 2))

/-- Paper label: `thm:conclusion-Lk-normalized-zeta-odd-projector`. -/
theorem paper_conclusion_lk_normalized_zeta_odd_projector :
    conclusion_lk_normalized_zeta_odd_projector_statement := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k s
    rcases Omega.POM.paper_pom_lk_spectral_zeta_dirichlet k s with
      ⟨_, hspectral, _, _⟩
    simp [conclusion_lk_normalized_zeta_odd_projector_normalized_zeta, hspectral]
  · intro k s
    rcases Omega.POM.paper_pom_lk_spectral_zeta_dirichlet k s with
      ⟨_, _, _, heven⟩
    unfold conclusion_lk_normalized_zeta_odd_projector_odd_projector
    rw [heven]
    ring
  · intro k s
    rcases Omega.POM.paper_pom_lk_spectral_zeta_dirichlet k s with
      ⟨_, _, hproxy, _⟩
    rw [hproxy]
    have hbase :
        (Real.pi / (2 * k + 1 : ℝ)) * (((2 * k + 1 : ℝ) / Real.pi)) = 1 := by
      have hpi : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
      have hk : (2 * k + 1 : ℝ) ≠ 0 := by positivity
      field_simp [hpi, hk]
    have hscale :
        (Real.pi / (2 * k + 1 : ℝ)) ^ (2 * s) * (((2 * k + 1 : ℝ) / Real.pi) ^ (2 * s)) = 1 := by
      rw [← Real.mul_rpow]
      · simp [hbase]
      · positivity
      · positivity
    calc
      (Real.pi / (2 * k + 1 : ℝ)) ^ (2 * s) *
          ((((2 * k + 1 : ℝ) / Real.pi) ^ (2 * s)) *
            Omega.POM.pom_lk_spectral_zeta_dirichlet_odd_sum k s)
          =
        ((Real.pi / (2 * k + 1 : ℝ)) ^ (2 * s) *
            (((2 * k + 1 : ℝ) / Real.pi) ^ (2 * s))) *
          Omega.POM.pom_lk_spectral_zeta_dirichlet_odd_sum k s := by ring
      _ = Omega.POM.pom_lk_spectral_zeta_dirichlet_odd_sum k s := by simp [hscale]
  · intro p
    exact (paper_conclusion_lk_fixed_index_hard_edge p).1

end

end Omega.Conclusion
