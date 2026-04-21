import Mathlib
import Omega.OperatorAlgebra.FoldCapacityCurveCompleteInvariant

namespace Omega.OperatorAlgebra

open scoped BigOperators

noncomputable section

/-- The maximal fiber multiplicity appearing in a finite spectrum package. -/
def foldGaugeMaxFiber (degrees : Finset ℕ) : ℕ :=
  degrees.sup id

/-- The finite Stieltjes--Dirichlet log-volume written in terms of tail counts. -/
def foldGaugeTailLogVolume (degrees : Finset ℕ) : ℝ :=
  Finset.sum (Finset.Icc 1 (foldGaugeMaxFiber degrees))
    (fun k => (foldTailCount degrees k : ℝ) * Real.log k)

/-- A concrete gauge-group volume whose logarithm is the Stieltjes--Dirichlet sum. -/
def foldGaugeGroupCard (degrees : Finset ℕ) : ℝ :=
  Real.exp (foldGaugeTailLogVolume degrees)

/-- Paper label: `thm:op-algebra-fold-gauge-log-volume-stieltjes`. The logarithmic gauge volume is
the tail-count Stieltjes sum, and then the first-difference formula for the capacity curve rewrites
the same expression in capacity-curve form. -/
theorem paper_op_algebra_fold_gauge_log_volume_stieltjes (degrees : Finset ℕ) :
    Real.log (foldGaugeGroupCard degrees) =
        Finset.sum (Finset.Icc 1 (foldGaugeMaxFiber degrees))
          (fun k => (foldTailCount degrees k : ℝ) * Real.log k) ∧
      Real.log (foldGaugeGroupCard degrees) =
        Finset.sum (Finset.Icc 1 (foldGaugeMaxFiber degrees))
          (fun k =>
            ((foldCapacityCurve degrees k - foldCapacityCurve degrees (k - 1) : ℕ) : ℝ) *
              Real.log k) := by
  refine ⟨?_, ?_⟩
  · simp [foldGaugeGroupCard, foldGaugeTailLogVolume]
  · calc
      Real.log (foldGaugeGroupCard degrees)
          = Finset.sum (Finset.Icc 1 (foldGaugeMaxFiber degrees))
              (fun k => (foldTailCount degrees k : ℝ) * Real.log k) := by
                simp [foldGaugeGroupCard, foldGaugeTailLogVolume]
      _ = Finset.sum (Finset.Icc 1 (foldGaugeMaxFiber degrees))
            (fun k =>
              ((foldCapacityCurve degrees k - foldCapacityCurve degrees (k - 1) : ℕ) : ℝ) *
                Real.log k) := by
            refine Finset.sum_congr rfl ?_
            intro k hk
            have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
            rw [show (foldTailCount degrees k : ℝ) =
                (((foldCapacityCurve degrees k - foldCapacityCurve degrees (k - 1) : ℕ)) : ℝ) by
                  exact congrArg (fun n : ℕ => (n : ℝ))
                    ((paper_op_algebra_capacity_curve_complete_invariant degrees).1 k hk1)]

end
end Omega.OperatorAlgebra
