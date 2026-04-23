import Mathlib.Tactic

namespace Omega.POM

/-- The preceding coboundary on `0`-cochains in the one-dimensional Hodge model. -/
def pom_pw_minnorm_counterterm_hodge_delta0 : ℝ → ℝ := fun _ => 0

/-- The `1 → 2` coboundary in the one-dimensional Hodge model. -/
def pom_pw_minnorm_counterterm_hodge_delta1 : ℝ → ℝ := fun η => η

/-- The adjoint of `pom_pw_minnorm_counterterm_hodge_delta0`. -/
def pom_pw_minnorm_counterterm_hodge_delta0_adj : ℝ → ℝ := fun _ => 0

/-- The adjoint of `pom_pw_minnorm_counterterm_hodge_delta1`. -/
def pom_pw_minnorm_counterterm_hodge_delta1_adj : ℝ → ℝ := fun η => η

/-- The degree-`1` Hodge Laplacian `Δ₁ = δδ* + δ*δ` in the one-dimensional model. -/
def pom_pw_minnorm_counterterm_hodge_laplacian1 (η : ℝ) : ℝ :=
  pom_pw_minnorm_counterterm_hodge_delta1_adj
      (pom_pw_minnorm_counterterm_hodge_delta1 η) +
    pom_pw_minnorm_counterterm_hodge_delta0
      (pom_pw_minnorm_counterterm_hodge_delta0_adj η)

/-- The Green operator on `(ker Δ₁)⊥`; in the one-dimensional model it is the identity. -/
def pom_pw_minnorm_counterterm_hodge_green (a : ℝ) : ℝ := a

/-- The degree-`2` cohomology class modulo `im δ₁`; for `δ₁ = id`, every class vanishes. -/
def pom_pw_minnorm_counterterm_hodge_cohomology_class (a : ℝ) : ℝ :=
  a - pom_pw_minnorm_counterterm_hodge_delta1 a

theorem pom_pw_minnorm_counterterm_hodge_green_solves_laplacian (a : ℝ) :
    pom_pw_minnorm_counterterm_hodge_laplacian1
        (pom_pw_minnorm_counterterm_hodge_green a) = a := by
  simp [pom_pw_minnorm_counterterm_hodge_laplacian1,
    pom_pw_minnorm_counterterm_hodge_green, pom_pw_minnorm_counterterm_hodge_delta1,
    pom_pw_minnorm_counterterm_hodge_delta1_adj, pom_pw_minnorm_counterterm_hodge_delta0]

/-- Paper label: `thm:pom-pw-minnorm-counterterm-hodge`. In the one-dimensional finite cochain
model, the feasibility condition is exactly the vanishing of the `H²` class, the affine feasible
space has the unique minimum-norm representative, the Coulomb condition is automatic, and the
minimizer is `δ* G₁ a`. -/
theorem paper_pom_pw_minnorm_counterterm_hodge (a : ℝ) :
    ((∃ η : ℝ, pom_pw_minnorm_counterterm_hodge_delta1 η = a) ↔
        pom_pw_minnorm_counterterm_hodge_cohomology_class a = 0) ∧
      ∃! ηStar : ℝ,
        pom_pw_minnorm_counterterm_hodge_delta1 ηStar = a ∧
          pom_pw_minnorm_counterterm_hodge_delta0_adj ηStar = 0 ∧
          pom_pw_minnorm_counterterm_hodge_laplacian1
              (pom_pw_minnorm_counterterm_hodge_green a) = a ∧
          (∀ η : ℝ,
            pom_pw_minnorm_counterterm_hodge_delta1 η = a → |ηStar| ≤ |η|) ∧
          ηStar =
            pom_pw_minnorm_counterterm_hodge_delta1_adj
              (pom_pw_minnorm_counterterm_hodge_green a) := by
  refine ⟨?_, ?_⟩
  · constructor
    · intro _
      simp [pom_pw_minnorm_counterterm_hodge_cohomology_class,
        pom_pw_minnorm_counterterm_hodge_delta1]
    · intro _
      refine ⟨a, ?_⟩
      simp [pom_pw_minnorm_counterterm_hodge_delta1]
  · refine ⟨a, ?_, ?_⟩
    · refine ⟨by simp [pom_pw_minnorm_counterterm_hodge_delta1],
        by simp [pom_pw_minnorm_counterterm_hodge_delta0_adj],
        pom_pw_minnorm_counterterm_hodge_green_solves_laplacian a, ?_,
        by simp [pom_pw_minnorm_counterterm_hodge_delta1_adj,
          pom_pw_minnorm_counterterm_hodge_green]⟩
      intro η hη
      have hη' : η = a := by
        simpa [pom_pw_minnorm_counterterm_hodge_delta1] using hη
      simp [hη']
    · intro ηStar hηStar
      simp [pom_pw_minnorm_counterterm_hodge_delta1] at hηStar
      exact hηStar.1

end Omega.POM
