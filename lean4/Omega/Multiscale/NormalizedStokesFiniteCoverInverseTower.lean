import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Multiscale

noncomputable section

/-- Concrete finite-cover inverse-tower bookkeeping for normalized bulk, boundary, and
differential integrals. Pullback along each covering map multiplies the corresponding integral by
the covering degree, so dividing by the cumulative degree produces a level-independent normalized
value. -/
structure NormalizedStokesFiniteCoverInverseTowerSystem where
  coverDegree : ℕ → ℕ
  coverDegree_two_le : ∀ n, 2 ≤ coverDegree n
  bulkIntegral : ℕ → ℝ
  boundaryIntegral : ℕ → ℝ
  differentialIntegral : ℕ → ℝ
  bulkPullback :
    ∀ n, bulkIntegral (n + 1) = (coverDegree n : ℝ) * bulkIntegral n
  boundaryPullback :
    ∀ n, boundaryIntegral (n + 1) = (coverDegree n : ℝ) * boundaryIntegral n
  differentialPullback :
    ∀ n, differentialIntegral (n + 1) = (coverDegree n : ℝ) * differentialIntegral n
  levelwiseStokes :
    ∀ n, differentialIntegral n = boundaryIntegral n

namespace NormalizedStokesFiniteCoverInverseTowerSystem

def cumulativeCoverDegree (S : NormalizedStokesFiniteCoverInverseTowerSystem) (n : ℕ) : ℝ :=
  Finset.prod (Finset.range n) fun j => (S.coverDegree j : ℝ)

def normalizedBulk (S : NormalizedStokesFiniteCoverInverseTowerSystem) (n : ℕ) : ℝ :=
  S.bulkIntegral n / cumulativeCoverDegree S n

def normalizedBoundary (S : NormalizedStokesFiniteCoverInverseTowerSystem) (n : ℕ) : ℝ :=
  S.boundaryIntegral n / cumulativeCoverDegree S n

def normalizedDifferential (S : NormalizedStokesFiniteCoverInverseTowerSystem) (n : ℕ) : ℝ :=
  S.differentialIntegral n / cumulativeCoverDegree S n

lemma cumulativeCoverDegree_pos (S : NormalizedStokesFiniteCoverInverseTowerSystem) (n : ℕ) :
    0 < cumulativeCoverDegree S n := by
  unfold cumulativeCoverDegree
  refine Finset.prod_pos ?_
  intro i hi
  have hdeg_pos_nat : 0 < S.coverDegree i := by
    exact lt_of_lt_of_le (by decide : 0 < 2) (S.coverDegree_two_le i)
  exact_mod_cast hdeg_pos_nat

lemma normalizedBulk_step (S : NormalizedStokesFiniteCoverInverseTowerSystem) (n : ℕ) :
    normalizedBulk S (n + 1) = normalizedBulk S n := by
  have hCum :
      cumulativeCoverDegree S (n + 1) =
        cumulativeCoverDegree S n * (S.coverDegree n : ℝ) := by
    unfold cumulativeCoverDegree
    rw [Finset.prod_range_succ]
  have hCumNz : cumulativeCoverDegree S n ≠ 0 := (cumulativeCoverDegree_pos S n).ne'
  have hDegPosNat : 0 < S.coverDegree n := by
    exact lt_of_lt_of_le (by decide : 0 < 2) (S.coverDegree_two_le n)
  have hDegNz : (S.coverDegree n : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hDegPosNat
  unfold normalizedBulk
  rw [S.bulkPullback n, hCum]
  field_simp [hCumNz, hDegNz]

lemma normalizedBoundary_step (S : NormalizedStokesFiniteCoverInverseTowerSystem) (n : ℕ) :
    normalizedBoundary S (n + 1) = normalizedBoundary S n := by
  have hCum :
      cumulativeCoverDegree S (n + 1) =
        cumulativeCoverDegree S n * (S.coverDegree n : ℝ) := by
    unfold cumulativeCoverDegree
    rw [Finset.prod_range_succ]
  have hCumNz : cumulativeCoverDegree S n ≠ 0 := (cumulativeCoverDegree_pos S n).ne'
  have hDegPosNat : 0 < S.coverDegree n := by
    exact lt_of_lt_of_le (by decide : 0 < 2) (S.coverDegree_two_le n)
  have hDegNz : (S.coverDegree n : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hDegPosNat
  unfold normalizedBoundary
  rw [S.boundaryPullback n, hCum]
  field_simp [hCumNz, hDegNz]

lemma normalizedDifferential_step (S : NormalizedStokesFiniteCoverInverseTowerSystem) (n : ℕ) :
    normalizedDifferential S (n + 1) = normalizedDifferential S n := by
  have hCum :
      cumulativeCoverDegree S (n + 1) =
        cumulativeCoverDegree S n * (S.coverDegree n : ℝ) := by
    unfold cumulativeCoverDegree
    rw [Finset.prod_range_succ]
  have hCumNz : cumulativeCoverDegree S n ≠ 0 := (cumulativeCoverDegree_pos S n).ne'
  have hDegPosNat : 0 < S.coverDegree n := by
    exact lt_of_lt_of_le (by decide : 0 < 2) (S.coverDegree_two_le n)
  have hDegNz : (S.coverDegree n : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hDegPosNat
  unfold normalizedDifferential
  rw [S.differentialPullback n, hCum]
  field_simp [hCumNz, hDegNz]

lemma normalizedStokes_levelwise (S : NormalizedStokesFiniteCoverInverseTowerSystem) (n : ℕ) :
    normalizedDifferential S n = normalizedBoundary S n := by
  unfold normalizedDifferential normalizedBoundary
  rw [S.levelwiseStokes n]

end NormalizedStokesFiniteCoverInverseTowerSystem

open NormalizedStokesFiniteCoverInverseTowerSystem

/-- Pullback scaling by the covering degree makes the normalized bulk and boundary integrals
level-independent; classical Stokes on each level then gives the normalized inverse-tower
identity.
    thm:app-normalized-stokes-finite-cover-inverse-tower -/
theorem paper_app_normalized_stokes_finite_cover_inverse_tower
    (S : NormalizedStokesFiniteCoverInverseTowerSystem) :
    (∀ n, normalizedBulk S (n + 1) = normalizedBulk S n) ∧
      (∀ n, normalizedBoundary S (n + 1) = normalizedBoundary S n) ∧
      (∀ n, normalizedDifferential S (n + 1) = normalizedDifferential S n) ∧
      (∀ n, normalizedDifferential S n = normalizedBoundary S n) := by
  exact ⟨normalizedBulk_step S, normalizedBoundary_step S, normalizedDifferential_step S,
    normalizedStokes_levelwise S⟩

end

end Omega.Multiscale
