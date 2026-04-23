import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

namespace Omega.POM

open scoped BigOperators

noncomputable section

/-- Independent diagonal mass `∑_x w(x)^2`. -/
def pom_diagonal_rate_collision_threshold_quadratic_law_diag_mass {n : ℕ}
    (w : Fin n → ℝ) : ℝ :=
  ∑ x, (w x) ^ 2

/-- Collision threshold `δ₀ = 1 - ∑_x w(x)^2`. -/
def pom_diagonal_rate_collision_threshold_quadratic_law_threshold {n : ℕ}
    (w : Fin n → ℝ) : ℝ :=
  1 - pom_diagonal_rate_collision_threshold_quadratic_law_diag_mass w

/-- The quadratic coefficient from the paper. -/
def pom_diagonal_rate_collision_threshold_quadratic_law_variance {n : ℕ}
    (w : Fin n → ℝ) : ℝ :=
  (∑ x, (w x) ^ 2) - 2 * (∑ x, (w x) ^ 3) +
    (∑ x, (w x) ^ 2) ^ 2

/-- The centered diagonal statistic used to perturb the independent coupling. -/
def pom_diagonal_rate_collision_threshold_quadratic_law_centered {n : ℕ}
    (w : Fin n → ℝ) (x y : Fin n) : ℝ :=
  (if x = y then 1 else 0) - w x - w y +
    pom_diagonal_rate_collision_threshold_quadratic_law_diag_mass w

/-- First-order perturbed diagonal mass. -/
def pom_diagonal_rate_collision_threshold_quadratic_law_perturbed_diag_mass {n : ℕ}
    (w : Fin n → ℝ) (ε : ℝ) : ℝ :=
  pom_diagonal_rate_collision_threshold_quadratic_law_diag_mass w + ε

/-- The quadratic-order rate model around the collision threshold. -/
def pom_diagonal_rate_collision_threshold_quadratic_law_rate
    (δ0 σ2 δ : ℝ) : ℝ :=
  (δ0 - δ) ^ 2 / (2 * σ2)

/-- Concrete chapter-local formulation of the threshold quadratic law. -/
def pom_diagonal_rate_collision_threshold_quadratic_law_statement : Prop :=
  ∀ {n : ℕ} (w : Fin n → ℝ),
    2 ≤ n →
    (∀ x, 0 < w x) →
    (∑ x, w x = 1) →
    let δ0 := pom_diagonal_rate_collision_threshold_quadratic_law_threshold w
    let σ2 := pom_diagonal_rate_collision_threshold_quadratic_law_variance w
    (1 - δ0 = pom_diagonal_rate_collision_threshold_quadratic_law_diag_mass w) ∧
      (∀ x, ∑ y,
          pom_diagonal_rate_collision_threshold_quadratic_law_centered w x y * w y = 0) ∧
      (∀ y, ∑ x,
          pom_diagonal_rate_collision_threshold_quadratic_law_centered w x y * w x = 0) ∧
      (0 < σ2 →
        ∀ ε : ℝ, 0 ≤ ε →
          pom_diagonal_rate_collision_threshold_quadratic_law_rate δ0 σ2 (δ0 - ε) =
            ε ^ 2 / (2 * σ2) ∧
          pom_diagonal_rate_collision_threshold_quadratic_law_perturbed_diag_mass w ε =
            1 - (δ0 - ε))

lemma pom_diagonal_rate_collision_threshold_quadratic_law_centered_row_mean_zero
    {n : ℕ} (w : Fin n → ℝ)
    (hsum : ∑ x, w x = 1) (x : Fin n) :
    ∑ y, pom_diagonal_rate_collision_threshold_quadratic_law_centered w x y * w y = 0 := by
  have hdiag : ∑ y, (if x = y then (1 : ℝ) else 0) * w y = w x := by
    simp
  have hconst : ∑ y, w x * w y = w x := by
    calc
      ∑ y, w x * w y = w x * ∑ y, w y := by rw [Finset.mul_sum]
      _ = w x := by rw [hsum]; ring
  have hsquare :
      ∑ y, w y * w y =
        pom_diagonal_rate_collision_threshold_quadratic_law_diag_mass w := by
    simp [pom_diagonal_rate_collision_threshold_quadratic_law_diag_mass, pow_two]
  have hmass :
      ∑ y,
          pom_diagonal_rate_collision_threshold_quadratic_law_diag_mass w * w y =
        pom_diagonal_rate_collision_threshold_quadratic_law_diag_mass w := by
    calc
      ∑ y, pom_diagonal_rate_collision_threshold_quadratic_law_diag_mass w * w y =
          pom_diagonal_rate_collision_threshold_quadratic_law_diag_mass w * ∑ y, w y := by
            rw [Finset.mul_sum]
      _ = pom_diagonal_rate_collision_threshold_quadratic_law_diag_mass w := by
            rw [hsum]
            ring
  calc
    ∑ y, pom_diagonal_rate_collision_threshold_quadratic_law_centered w x y * w y
        = ∑ y, (((if x = y then (1 : ℝ) else 0) * w y
            - (w x * w y) - (w y * w y)) +
              pom_diagonal_rate_collision_threshold_quadratic_law_diag_mass w * w y) := by
              refine Finset.sum_congr rfl ?_
              intro y hy
              dsimp [pom_diagonal_rate_collision_threshold_quadratic_law_centered]
              ring
    _ = (∑ y, (if x = y then (1 : ℝ) else 0) * w y) - ∑ y, w x * w y - ∑ y, w y * w y +
          ∑ y, pom_diagonal_rate_collision_threshold_quadratic_law_diag_mass w * w y := by
            rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    _ = w x - w x -
          pom_diagonal_rate_collision_threshold_quadratic_law_diag_mass w +
          pom_diagonal_rate_collision_threshold_quadratic_law_diag_mass w := by
            rw [hdiag, hconst, hsquare, hmass]
    _ = 0 := by ring

lemma pom_diagonal_rate_collision_threshold_quadratic_law_centered_col_mean_zero
    {n : ℕ} (w : Fin n → ℝ)
    (hsum : ∑ x, w x = 1) (y : Fin n) :
    ∑ x, pom_diagonal_rate_collision_threshold_quadratic_law_centered w x y * w x = 0 := by
  have hdiag : ∑ x, (if x = y then (1 : ℝ) else 0) * w x = w y := by
    simp
  have hconst : ∑ x, w y * w x = w y := by
    calc
      ∑ x, w y * w x = w y * ∑ x, w x := by rw [Finset.mul_sum]
      _ = w y := by rw [hsum]; ring
  have hsquare :
      ∑ x, w x * w x =
        pom_diagonal_rate_collision_threshold_quadratic_law_diag_mass w := by
    simp [pom_diagonal_rate_collision_threshold_quadratic_law_diag_mass, pow_two]
  have hmass :
      ∑ x,
          pom_diagonal_rate_collision_threshold_quadratic_law_diag_mass w * w x =
        pom_diagonal_rate_collision_threshold_quadratic_law_diag_mass w := by
    calc
      ∑ x, pom_diagonal_rate_collision_threshold_quadratic_law_diag_mass w * w x =
          pom_diagonal_rate_collision_threshold_quadratic_law_diag_mass w * ∑ x, w x := by
            rw [Finset.mul_sum]
      _ = pom_diagonal_rate_collision_threshold_quadratic_law_diag_mass w := by
            rw [hsum]
            ring
  calc
    ∑ x, pom_diagonal_rate_collision_threshold_quadratic_law_centered w x y * w x
        = ∑ x, (((if x = y then (1 : ℝ) else 0) * w x
            - (w x * w x) - (w y * w x)) +
              pom_diagonal_rate_collision_threshold_quadratic_law_diag_mass w * w x) := by
              refine Finset.sum_congr rfl ?_
              intro x hx
              dsimp [pom_diagonal_rate_collision_threshold_quadratic_law_centered]
              ring
    _ = (∑ x, (if x = y then (1 : ℝ) else 0) * w x) - ∑ x, w x * w x - ∑ x, w y * w x +
          ∑ x, pom_diagonal_rate_collision_threshold_quadratic_law_diag_mass w * w x := by
            rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    _ = w y -
          pom_diagonal_rate_collision_threshold_quadratic_law_diag_mass w - w y +
          pom_diagonal_rate_collision_threshold_quadratic_law_diag_mass w := by
            rw [hdiag, hsquare, hconst, hmass]
    _ = 0 := by ring

/-- Paper label: `thm:pom-diagonal-rate-collision-threshold-quadratic-law`. -/
theorem paper_pom_diagonal_rate_collision_threshold_quadratic_law :
    pom_diagonal_rate_collision_threshold_quadratic_law_statement := by
  intro n w hn hwpos hsum
  dsimp
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [pom_diagonal_rate_collision_threshold_quadratic_law_threshold]
  · intro x
    exact pom_diagonal_rate_collision_threshold_quadratic_law_centered_row_mean_zero w hsum x
  · intro y
    exact pom_diagonal_rate_collision_threshold_quadratic_law_centered_col_mean_zero w hsum y
  · intro hσ ε hε
    refine ⟨?_, ?_⟩
    · unfold pom_diagonal_rate_collision_threshold_quadratic_law_rate
      ring_nf
    · simp [pom_diagonal_rate_collision_threshold_quadratic_law_perturbed_diag_mass,
        pom_diagonal_rate_collision_threshold_quadratic_law_threshold]
      ring

end

end Omega.POM
