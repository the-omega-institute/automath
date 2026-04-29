import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- Concrete finite-grid data for the strong holography Lipschitz-stability estimate. The first
coordinate is the chain direction `0, …, length`; the transverse direction is finite, and every
fiber is anchored to zero on the left boundary. -/
structure conclusion_strong_holography_lipschitz_stability_Data where
  conclusion_strong_holography_lipschitz_stability_Transverse : Type
  conclusion_strong_holography_lipschitz_stability_instFintypeTransverse :
    Fintype conclusion_strong_holography_lipschitz_stability_Transverse
  conclusion_strong_holography_lipschitz_stability_instDecidableEqTransverse :
    DecidableEq conclusion_strong_holography_lipschitz_stability_Transverse
  conclusion_strong_holography_lipschitz_stability_length : ℕ
  conclusion_strong_holography_lipschitz_stability_scale : ℝ
  conclusion_strong_holography_lipschitz_stability_scale_nonneg :
    0 ≤ conclusion_strong_holography_lipschitz_stability_scale
  conclusion_strong_holography_lipschitz_stability_state :
    ℕ → conclusion_strong_holography_lipschitz_stability_Transverse → ℝ
  conclusion_strong_holography_lipschitz_stability_left_boundary_zero :
    ∀ y, conclusion_strong_holography_lipschitz_stability_state 0 y = 0

attribute [instance]
  conclusion_strong_holography_lipschitz_stability_Data.conclusion_strong_holography_lipschitz_stability_instFintypeTransverse
attribute [instance]
  conclusion_strong_holography_lipschitz_stability_Data.conclusion_strong_holography_lipschitz_stability_instDecidableEqTransverse

/-- The first-coordinate boundary jump on one transverse fiber. -/
def conclusion_strong_holography_lipschitz_stability_boundaryJump
    (D : conclusion_strong_holography_lipschitz_stability_Data)
    (i : ℕ) (y : D.conclusion_strong_holography_lipschitz_stability_Transverse) : ℝ :=
  ‖D.conclusion_strong_holography_lipschitz_stability_state (i + 1) y -
    D.conclusion_strong_holography_lipschitz_stability_state i y‖

/-- The bulk `ℓ¹` mass on one transverse fiber. -/
def conclusion_strong_holography_lipschitz_stability_fiberBulk
    (D : conclusion_strong_holography_lipschitz_stability_Data)
    (y : D.conclusion_strong_holography_lipschitz_stability_Transverse) : ℝ :=
  Finset.sum
    (Finset.range (D.conclusion_strong_holography_lipschitz_stability_length + 1))
    (fun i => ‖D.conclusion_strong_holography_lipschitz_stability_state i y‖)

/-- The first-coordinate boundary variation on one transverse fiber. -/
def conclusion_strong_holography_lipschitz_stability_fiberBoundary
    (D : conclusion_strong_holography_lipschitz_stability_Data)
    (y : D.conclusion_strong_holography_lipschitz_stability_Transverse) : ℝ :=
  Finset.sum
    (Finset.range D.conclusion_strong_holography_lipschitz_stability_length)
    (fun i => conclusion_strong_holography_lipschitz_stability_boundaryJump D i y)

/-- Scaled bulk volume on the finite polycube grid. -/
def conclusion_strong_holography_lipschitz_stability_scaledBulk
    (D : conclusion_strong_holography_lipschitz_stability_Data) : ℝ :=
  D.conclusion_strong_holography_lipschitz_stability_scale *
    Finset.sum Finset.univ
      (fun y : D.conclusion_strong_holography_lipschitz_stability_Transverse =>
        conclusion_strong_holography_lipschitz_stability_fiberBulk D y)

/-- Scaled boundary-area budget with the chain-length Lipschitz factor. -/
def conclusion_strong_holography_lipschitz_stability_scaledBoundary
    (D : conclusion_strong_holography_lipschitz_stability_Data) : ℝ :=
  D.conclusion_strong_holography_lipschitz_stability_scale *
    ((D.conclusion_strong_holography_lipschitz_stability_length + 1 : ℝ) *
      Finset.sum Finset.univ
        (fun y : D.conclusion_strong_holography_lipschitz_stability_Transverse =>
          conclusion_strong_holography_lipschitz_stability_fiberBoundary D y))

/-- Paper-facing statement: scaled finite-grid volume is controlled by the first-coordinate
boundary variation, uniformly over all transverse fibers. -/
def conclusion_strong_holography_lipschitz_stability_statement
    (D : conclusion_strong_holography_lipschitz_stability_Data) : Prop :=
  conclusion_strong_holography_lipschitz_stability_scaledBulk D ≤
    conclusion_strong_holography_lipschitz_stability_scaledBoundary D

lemma conclusion_strong_holography_lipschitz_stability_prefix_bound
    (a : ℕ → ℝ) (h0 : a 0 = 0) (n : ℕ) :
    ‖a n‖ ≤ Finset.sum (Finset.range n) (fun i => ‖a (i + 1) - a i‖) := by
  induction n with
  | zero =>
      simp [h0]
  | succ n ih =>
      have htri : ‖a (n + 1)‖ ≤ ‖a n‖ + ‖a (n + 1) - a n‖ := by
        calc
          ‖a (n + 1)‖ = ‖a n + (a (n + 1) - a n)‖ := by ring_nf
          _ ≤ ‖a n‖ + ‖a (n + 1) - a n‖ := norm_add_le _ _
      rw [Finset.sum_range_succ]
      linarith

lemma conclusion_strong_holography_lipschitz_stability_fiber_bound
    (D : conclusion_strong_holography_lipschitz_stability_Data)
    (y : D.conclusion_strong_holography_lipschitz_stability_Transverse) :
    conclusion_strong_holography_lipschitz_stability_fiberBulk D y ≤
      (D.conclusion_strong_holography_lipschitz_stability_length + 1 : ℝ) *
        conclusion_strong_holography_lipschitz_stability_fiberBoundary D y := by
  classical
  let L := D.conclusion_strong_holography_lipschitz_stability_length
  let a : ℕ → ℝ := fun i =>
    D.conclusion_strong_holography_lipschitz_stability_state i y
  have hterm :
      ∀ i ∈ Finset.range (L + 1),
        ‖a i‖ ≤ Finset.sum (Finset.range L) (fun j => ‖a (j + 1) - a j‖) := by
    intro i hi
    have hiL : i ≤ L := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hprefix :
        ‖a i‖ ≤ Finset.sum (Finset.range i) (fun j => ‖a (j + 1) - a j‖) :=
      conclusion_strong_holography_lipschitz_stability_prefix_bound a
        (D.conclusion_strong_holography_lipschitz_stability_left_boundary_zero y) i
    have hsubset : Finset.range i ⊆ Finset.range L := by
      intro j hj
      exact Finset.mem_range.mpr (Nat.lt_of_lt_of_le (Finset.mem_range.mp hj) hiL)
    have hprefix_le :
        Finset.sum (Finset.range i) (fun j => ‖a (j + 1) - a j‖) ≤
          Finset.sum (Finset.range L) (fun j => ‖a (j + 1) - a j‖) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (by intro x _ _; positivity)
    exact hprefix.trans hprefix_le
  have hsum :
      Finset.sum (Finset.range (L + 1)) (fun i => ‖a i‖) ≤
        Finset.sum (Finset.range (L + 1))
          (fun _i => Finset.sum (Finset.range L) (fun j => ‖a (j + 1) - a j‖)) := by
    exact Finset.sum_le_sum hterm
  simpa [conclusion_strong_holography_lipschitz_stability_fiberBulk,
    conclusion_strong_holography_lipschitz_stability_fiberBoundary,
    conclusion_strong_holography_lipschitz_stability_boundaryJump, L, a, mul_comm] using hsum

/-- Paper label: `thm:conclusion-strong-holography-lipschitz-stability`. -/
theorem paper_conclusion_strong_holography_lipschitz_stability
    (D : conclusion_strong_holography_lipschitz_stability_Data) :
    conclusion_strong_holography_lipschitz_stability_statement D := by
  classical
  have hfiber :
      Finset.sum Finset.univ
          (fun y : D.conclusion_strong_holography_lipschitz_stability_Transverse =>
            conclusion_strong_holography_lipschitz_stability_fiberBulk D y) ≤
        Finset.sum Finset.univ
          (fun y : D.conclusion_strong_holography_lipschitz_stability_Transverse =>
            (D.conclusion_strong_holography_lipschitz_stability_length + 1 : ℝ) *
              conclusion_strong_holography_lipschitz_stability_fiberBoundary D y) := by
    refine Finset.sum_le_sum ?_
    intro y _hy
    exact conclusion_strong_holography_lipschitz_stability_fiber_bound D y
  have hfiber' :
      Finset.sum Finset.univ
          (fun y : D.conclusion_strong_holography_lipschitz_stability_Transverse =>
            conclusion_strong_holography_lipschitz_stability_fiberBulk D y) ≤
        (D.conclusion_strong_holography_lipschitz_stability_length + 1 : ℝ) *
          Finset.sum Finset.univ
            (fun y : D.conclusion_strong_holography_lipschitz_stability_Transverse =>
              conclusion_strong_holography_lipschitz_stability_fiberBoundary D y) := by
    simpa [Finset.mul_sum] using hfiber
  unfold conclusion_strong_holography_lipschitz_stability_statement
    conclusion_strong_holography_lipschitz_stability_scaledBulk
    conclusion_strong_holography_lipschitz_stability_scaledBoundary
  exact mul_le_mul_of_nonneg_left hfiber'
    D.conclusion_strong_holography_lipschitz_stability_scale_nonneg

end Omega.Conclusion
