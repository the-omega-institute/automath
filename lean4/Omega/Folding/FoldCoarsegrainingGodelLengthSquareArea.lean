import Mathlib.Tactic
import Omega.Folding.CoarsegrainingQuadraticStokesAreaRigidity
import Omega.Folding.FoldHypercubeGodelLengthEnergyUpperbound

namespace Omega.Folding

noncomputable section

open scoped BigOperators

/-- Paper label: `cor:fold-coarsegraining-godel-length-square-area`. Applying the single-fiber
Gödel-length energy estimate to every coarsegraining fiber and summing the resulting square bounds
gives the claimed quadratic Stokes-area control. -/
theorem paper_fold_coarsegraining_godel_length_square_area
    {n : ℕ} {X : Type*} [Fintype X] [DecidableEq X] (f : Omega.Word n → X) (p : Fin n → ℕ) :
    ∑ x, (hypercubeGodelLength (coarsegrainingFiber f x) p) ^ 2 ≤
      (2 : ℝ) ^ n * coarsegrainingWeightedCutCount f (fun _ => (1 : ℝ)) *
        ∑ i : Fin n, (Real.log (p i)) ^ 2 := by
  let logSq : ℝ := ∑ i : Fin n, (Real.log (p i)) ^ 2
  have hlogSq_nonneg : 0 ≤ logSq := by
    unfold logSq
    refine Finset.sum_nonneg ?_
    intro i _
    positivity
  have hfiber :
      ∀ x : X,
        (hypercubeGodelLength (coarsegrainingFiber f x) p) ^ 2 ≤
          ((2 : ℝ) ^ (n - 1) * coarsegrainingFiberEnergy f (fun _ => (1 : ℝ)) x) * logSq := by
    intro x
    have henergy :
        (∑ i : Fin n, (1 : ℝ) * (hypercubeCoordinateBias (coarsegrainingFiber f x) i : ℝ) ^ 2) ≤
          (2 : ℝ) ^ (n - 1) * coarsegrainingFiberEnergy f (fun _ => (1 : ℝ)) x := by
      simpa [coarsegrainingFiberEnergy] using
        paper_fold_hypercube_weighted_energy_ellipsoid_bias
          (S := coarsegrainingFiber f x) (w := fun _ => (1 : ℝ)) (hw := fun _ => by norm_num)
    have henergy_nonneg :
        0 ≤ (2 : ℝ) ^ (n - 1) * coarsegrainingFiberEnergy f (fun _ => (1 : ℝ)) x :=
      le_trans
        (by
          refine Finset.sum_nonneg ?_
          intro i _
          positivity)
        henergy
    have hlength_nonneg : 0 ≤ hypercubeGodelLength (coarsegrainingFiber f x) p := by
      unfold hypercubeGodelLength
      refine Finset.sum_nonneg ?_
      intro i _
      exact mul_nonneg (abs_nonneg _) (Real.log_natCast_nonneg _)
    have hbound :
        hypercubeGodelLength (coarsegrainingFiber f x) p ≤
          Real.sqrt ((2 : ℝ) ^ (n - 1) * coarsegrainingFiberEnergy f (fun _ => (1 : ℝ)) x) *
            Real.sqrt logSq := by
      simpa [logSq, coarsegrainingFiberEnergy, hypercubeGodelLength] using
        paper_fold_hypercube_godel_length_energy_upperbound
          (n := n)
          (bias := fun i => (hypercubeCoordinateBias (coarsegrainingFiber f x) i : ℝ))
          (w := fun _ => (1 : ℝ))
          (logq := fun i => Real.log (p i))
          (E := coarsegrainingFiberEnergy f (fun _ => (1 : ℝ)) x)
          (hpos := fun _ => by norm_num)
          (henergy := henergy)
    have hrhs_nonneg :
        0 ≤
          Real.sqrt ((2 : ℝ) ^ (n - 1) * coarsegrainingFiberEnergy f (fun _ => (1 : ℝ)) x) *
            Real.sqrt logSq :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have hsq :
        (hypercubeGodelLength (coarsegrainingFiber f x) p) ^ 2 ≤
          (Real.sqrt ((2 : ℝ) ^ (n - 1) * coarsegrainingFiberEnergy f (fun _ => (1 : ℝ)) x) *
            Real.sqrt logSq) ^ 2 := by
      simpa [pow_two] using mul_self_le_mul_self hlength_nonneg hbound
    calc
      (hypercubeGodelLength (coarsegrainingFiber f x) p) ^ 2 ≤
          (Real.sqrt ((2 : ℝ) ^ (n - 1) * coarsegrainingFiberEnergy f (fun _ => (1 : ℝ)) x) *
            Real.sqrt logSq) ^ 2 := hsq
      _ = ((2 : ℝ) ^ (n - 1) * coarsegrainingFiberEnergy f (fun _ => (1 : ℝ)) x) * logSq := by
            calc
              (Real.sqrt ((2 : ℝ) ^ (n - 1) * coarsegrainingFiberEnergy f (fun _ => (1 : ℝ)) x) *
                  Real.sqrt logSq) ^ 2
                  = (Real.sqrt ((2 : ℝ) ^ (n - 1) * coarsegrainingFiberEnergy f (fun _ => (1 : ℝ)) x)) ^ 2 *
                      (Real.sqrt logSq) ^ 2 := by ring
              _ = ((2 : ℝ) ^ (n - 1) * coarsegrainingFiberEnergy f (fun _ => (1 : ℝ)) x) * logSq := by
                    rw [Real.sq_sqrt henergy_nonneg, Real.sq_sqrt hlogSq_nonneg]
  calc
    ∑ x, (hypercubeGodelLength (coarsegrainingFiber f x) p) ^ 2
        ≤ ∑ x, ((2 : ℝ) ^ (n - 1) * coarsegrainingFiberEnergy f (fun _ => (1 : ℝ)) x) * logSq := by
            exact Finset.sum_le_sum fun x _ => hfiber x
    _ = logSq * ∑ x, (2 : ℝ) ^ (n - 1) * coarsegrainingFiberEnergy f (fun _ => (1 : ℝ)) x := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro x _
          ring
    _ = logSq * ((2 : ℝ) ^ (n - 1) * ∑ x, coarsegrainingFiberEnergy f (fun _ => (1 : ℝ)) x) := by
          congr 1
          rw [← Finset.mul_sum]
    _ = logSq * ((2 : ℝ) ^ n * coarsegrainingWeightedCutCount f (fun _ => (1 : ℝ))) := by
          rw [coarsegrainingWeightedCutCount]
          have hpow_ne : (2 : ℝ) ^ n ≠ 0 := by positivity
          field_simp [hpow_ne]
    _ = (2 : ℝ) ^ n * coarsegrainingWeightedCutCount f (fun _ => (1 : ℝ)) * logSq := by ring
    _ = (2 : ℝ) ^ n * coarsegrainingWeightedCutCount f (fun _ => (1 : ℝ)) *
          ∑ i : Fin n, (Real.log (p i)) ^ 2 := by
            rfl

end

end Omega.Folding
