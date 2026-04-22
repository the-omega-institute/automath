import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.POM

open scoped BigOperators

/-- A finite-fiber weighted conditional-expectation package over a sigma-type family of fibers.
The fiber over `y` is indexed by `Fin (fiberSize y)`, the weighted observable is `observable`,
and `condexp y` is required to reproduce the weighted first moment on each fiber. -/
structure WeightedCondexpVarianceData where
  Y : Type
  [fintypeY : Fintype Y]
  [decidableEqY : DecidableEq Y]
  fiberSize : Y → ℕ
  weight : (Σ y : Y, Fin (fiberSize y)) → ℝ
  observable : (Σ y : Y, Fin (fiberSize y)) → ℝ
  condexp : Y → ℝ
  condexp_spec :
    ∀ y, (∑ i : Fin (fiberSize y), weight ⟨y, i⟩ * observable ⟨y, i⟩) =
      condexp y * ∑ i : Fin (fiberSize y), weight ⟨y, i⟩

attribute [instance] WeightedCondexpVarianceData.fintypeY
attribute [instance] WeightedCondexpVarianceData.decidableEqY

namespace WeightedCondexpVarianceData

/-- The fiberwise conditional expectation lifted back to the full sigma-type state space. -/
def liftedCondexp (D : WeightedCondexpVarianceData) :
    (Σ y : D.Y, Fin (D.fiberSize y)) → ℝ :=
  fun ω => D.condexp ω.1

/-- The residual after subtracting the fiberwise conditional expectation. -/
def residual (D : WeightedCondexpVarianceData) :
    (Σ y : D.Y, Fin (D.fiberSize y)) → ℝ :=
  fun ω => D.observable ω - D.liftedCondexp ω

/-- The lifted conditional expectation is constant on each fiber. -/
def fiberwiseConstantCondexp (D : WeightedCondexpVarianceData) : Prop :=
  ∀ ω ω' : Σ y : D.Y, Fin (D.fiberSize y), ω.1 = ω'.1 → D.liftedCondexp ω = D.liftedCondexp ω'

/-- The weighted residual is orthogonal to the lifted conditional expectation. -/
def orthogonalProjection (D : WeightedCondexpVarianceData) : Prop :=
  (∑ ω : Σ y : D.Y, Fin (D.fiberSize y),
      D.weight ω * D.residual ω * D.liftedCondexp ω) = 0

/-- Weighted Pythagorean decomposition of the squared observable into the squared lifted
conditional expectation plus the squared residual. -/
def varianceSplit (D : WeightedCondexpVarianceData) : Prop :=
  (∑ ω : Σ y : D.Y, Fin (D.fiberSize y), D.weight ω * D.observable ω ^ 2) =
    (∑ ω : Σ y : D.Y, Fin (D.fiberSize y), D.weight ω * D.liftedCondexp ω ^ 2) +
      ∑ ω : Σ y : D.Y, Fin (D.fiberSize y), D.weight ω * D.residual ω ^ 2

lemma fiber_centered_sum (D : WeightedCondexpVarianceData) (y : D.Y) :
    (∑ i : Fin (D.fiberSize y), D.weight ⟨y, i⟩ * (D.observable ⟨y, i⟩ - D.condexp y)) = 0 := by
  calc
    (∑ i : Fin (D.fiberSize y), D.weight ⟨y, i⟩ * (D.observable ⟨y, i⟩ - D.condexp y)) =
        (∑ i : Fin (D.fiberSize y),
          (D.weight ⟨y, i⟩ * D.observable ⟨y, i⟩ - D.weight ⟨y, i⟩ * D.condexp y)) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            ring
    _ = (∑ i : Fin (D.fiberSize y), D.weight ⟨y, i⟩ * D.observable ⟨y, i⟩) -
          ∑ i : Fin (D.fiberSize y), D.weight ⟨y, i⟩ * D.condexp y := by
            rw [Finset.sum_sub_distrib]
    _ = D.condexp y * ∑ i : Fin (D.fiberSize y), D.weight ⟨y, i⟩ -
          D.condexp y * ∑ i : Fin (D.fiberSize y), D.weight ⟨y, i⟩ := by
            rw [D.condexp_spec]
            congr 1
            calc
              (∑ i : Fin (D.fiberSize y), D.weight ⟨y, i⟩ * D.condexp y) =
                  ∑ i : Fin (D.fiberSize y), D.condexp y * D.weight ⟨y, i⟩ := by
                    refine Finset.sum_congr rfl ?_
                    intro i hi
                    ring
              _ = D.condexp y * ∑ i : Fin (D.fiberSize y), D.weight ⟨y, i⟩ := by
                    rw [Finset.mul_sum]
    _ = 0 := by ring

lemma orthogonalProjection_proof (D : WeightedCondexpVarianceData) : D.orthogonalProjection := by
  unfold orthogonalProjection
  rw [Fintype.sum_sigma]
  refine Finset.sum_eq_zero ?_
  intro y hy
  have hy_factor :
      (∑ i : Fin (D.fiberSize y), D.weight ⟨y, i⟩ * D.residual ⟨y, i⟩ * D.liftedCondexp ⟨y, i⟩) =
        D.condexp y *
          ∑ i : Fin (D.fiberSize y), D.weight ⟨y, i⟩ * (D.observable ⟨y, i⟩ - D.condexp y) := by
    calc
      (∑ i : Fin (D.fiberSize y), D.weight ⟨y, i⟩ * D.residual ⟨y, i⟩ * D.liftedCondexp ⟨y, i⟩) =
          ∑ i : Fin (D.fiberSize y),
            D.condexp y * (D.weight ⟨y, i⟩ * (D.observable ⟨y, i⟩ - D.condexp y)) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              simp [residual, liftedCondexp]
              ring
      _ = D.condexp y *
            ∑ i : Fin (D.fiberSize y), D.weight ⟨y, i⟩ * (D.observable ⟨y, i⟩ - D.condexp y) := by
            rw [Finset.mul_sum]
  rw [hy_factor, D.fiber_centered_sum y]
  ring

lemma varianceSplit_proof (D : WeightedCondexpVarianceData) : D.varianceSplit := by
  unfold varianceSplit
  calc
    (∑ ω : Σ y : D.Y, Fin (D.fiberSize y), D.weight ω * D.observable ω ^ 2) =
        ∑ ω : Σ y : D.Y, Fin (D.fiberSize y),
          (D.weight ω * D.liftedCondexp ω ^ 2 +
            ((2 : ℝ) * (D.weight ω * D.residual ω * D.liftedCondexp ω) +
              D.weight ω * D.residual ω ^ 2)) := by
              refine Finset.sum_congr rfl ?_
              intro ω hω
              simp [residual]
              ring
    _ = (∑ ω : Σ y : D.Y, Fin (D.fiberSize y), D.weight ω * D.liftedCondexp ω ^ 2) +
          ∑ ω : Σ y : D.Y, Fin (D.fiberSize y),
            ((2 : ℝ) * (D.weight ω * D.residual ω * D.liftedCondexp ω) +
              D.weight ω * D.residual ω ^ 2) := by
                rw [Finset.sum_add_distrib]
    _ = (∑ ω : Σ y : D.Y, Fin (D.fiberSize y), D.weight ω * D.liftedCondexp ω ^ 2) +
          ((∑ ω : Σ y : D.Y, Fin (D.fiberSize y),
              (2 : ℝ) * (D.weight ω * D.residual ω * D.liftedCondexp ω)) +
            ∑ ω : Σ y : D.Y, Fin (D.fiberSize y), D.weight ω * D.residual ω ^ 2) := by
                rw [Finset.sum_add_distrib]
    _ = (∑ ω : Σ y : D.Y, Fin (D.fiberSize y), D.weight ω * D.liftedCondexp ω ^ 2) +
          (((2 : ℝ) *
              ∑ ω : Σ y : D.Y, Fin (D.fiberSize y),
                D.weight ω * D.residual ω * D.liftedCondexp ω) +
            ∑ ω : Σ y : D.Y, Fin (D.fiberSize y), D.weight ω * D.residual ω ^ 2) := by
                congr 1
                rw [Finset.mul_sum]
    _ = (∑ ω : Σ y : D.Y, Fin (D.fiberSize y), D.weight ω * D.liftedCondexp ω ^ 2) +
          ∑ ω : Σ y : D.Y, Fin (D.fiberSize y), D.weight ω * D.residual ω ^ 2 := by
            rw [D.orthogonalProjection_proof]
            ring

end WeightedCondexpVarianceData

open WeightedCondexpVarianceData

/-- Weighted conditional expectation over finite fibers is fiberwise constant, orthogonal to the
residual, and yields the exact finite weighted variance decomposition.
    prop:pom-weighted-condexp-variance -/
theorem paper_pom_weighted_condexp_variance (D : WeightedCondexpVarianceData) :
    D.fiberwiseConstantCondexp ∧ D.orthogonalProjection ∧ D.varianceSplit := by
  refine ⟨?_, D.orthogonalProjection_proof, D.varianceSplit_proof⟩
  intro ω ω' hω
  simp [liftedCondexp, hω]

end Omega.POM
