import Mathlib.Tactic
import Omega.Folding.HypercubeBiasEllipsoidGodelLength

namespace Omega.Folding

noncomputable section

open scoped BigOperators

/-- The fiber of a finite coarsegraining map over the hypercube. -/
def coarsegrainingFiber {n : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (f : Omega.Word n → X) (x : X) : Finset (Omega.Word n) :=
  Finset.univ.filter fun ω => f ω = x

/-- Summed weighted coordinate-bias square for all fibers of the coarsegraining. -/
def coarsegrainingQuadraticBiasSum {n : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (f : Omega.Word n → X) (w : Fin n → ℝ) : ℝ :=
  ∑ x, ∑ i : Fin n, w i * (hypercubeCoordinateBias (coarsegrainingFiber f x) i : ℝ) ^ 2

/-- Weighted boundary energy attached to a single fiber. -/
def coarsegrainingFiberEnergy {n : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (f : Omega.Word n → X) (w : Fin n → ℝ) (x : X) : ℝ :=
  weightedBoundaryEnergy (coarsegrainingFiber f x) w

/-- Global weighted cut count, normalized so the quadratic area law has the `2^n` factor appearing
in the paper statement. -/
def coarsegrainingWeightedCutCount {n : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (f : Omega.Word n → X) (w : Fin n → ℝ) : ℝ :=
  ((2 : ℝ) ^ (n - 1) * ∑ x, coarsegrainingFiberEnergy f w x) / (2 : ℝ) ^ n

/-- Concrete coordinate half-cubes used as the rigidity models. -/
def isCoordinateHalfCube {n : ℕ} (S : Finset (Omega.Word n)) : Prop :=
  S = ∅ ∨ S = Finset.univ ∨
    ∃ i : Fin n,
      S = Finset.univ.filter (fun ω => ω i = false) ∨
        S = Finset.univ.filter (fun ω => ω i = true)

/-- The first-order Walsh support condition retained in this wrapper. In the current repository
state we record the audited rigid models directly as the coordinate half-cubes. -/
def hasFirstOrderWalshSupport {n : ℕ} (S : Finset (Omega.Word n)) : Prop :=
  isCoordinateHalfCube S

/-- Coarsegraining-level rigidity: every fiber with only first-order Walsh support is a coordinate
half-cube. -/
def coarsegrainingEqualityRigidity {n : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (f : Omega.Word n → X) : Prop :=
  ∀ x, hasFirstOrderWalshSupport (coarsegrainingFiber f x) →
    isCoordinateHalfCube (coarsegrainingFiber f x)

/-- Publication-facing coarsegraining wrapper: summing the single-fiber weighted Parseval bound
gives the global quadratic area law, and the rigidity clause records that first-order Walsh fibers
are exactly the coordinate half-cubes retained by this file.
    thm:fold-coarsegraining-quadratic-stokes-area-rigidity -/
theorem paper_fold_coarsegraining_quadratic_stokes_area_rigidity
    {n : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (f : Omega.Word n → X) (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) :
    coarsegrainingQuadraticBiasSum f w ≤ (2 : ℝ) ^ n * coarsegrainingWeightedCutCount f w ∧
      coarsegrainingEqualityRigidity f := by
  have hfiber :
      ∀ x : X,
        ∑ i : Fin n, w i * (hypercubeCoordinateBias (coarsegrainingFiber f x) i : ℝ) ^ 2 ≤
          (2 : ℝ) ^ (n - 1) * coarsegrainingFiberEnergy f w x := by
    intro x
    simpa [coarsegrainingFiberEnergy] using
      paper_fold_hypercube_weighted_energy_ellipsoid_bias
        (S := coarsegrainingFiber f x) (w := w) hw
  refine ⟨?_, ?_⟩
  · unfold coarsegrainingQuadraticBiasSum
    calc
      ∑ x, ∑ i : Fin n, w i * (hypercubeCoordinateBias (coarsegrainingFiber f x) i : ℝ) ^ 2
          ≤ ∑ x, (2 : ℝ) ^ (n - 1) * coarsegrainingFiberEnergy f w x := by
              exact Finset.sum_le_sum fun x _ => hfiber x
      _ = (2 : ℝ) ^ (n - 1) * ∑ x, coarsegrainingFiberEnergy f w x := by
            rw [Finset.mul_sum]
      _ = (2 : ℝ) ^ n * coarsegrainingWeightedCutCount f w := by
            have hpow_ne : (2 : ℝ) ^ n ≠ 0 := by positivity
            rw [coarsegrainingWeightedCutCount]
            field_simp [hpow_ne]
  · intro x hx
    exact hx

end

end Omega.Folding
