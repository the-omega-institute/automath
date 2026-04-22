import Mathlib.Data.Set.Basic
import Mathlib.Tactic
import Omega.OperatorAlgebra.FoldConditionalExpectation

namespace Omega.OperatorAlgebra

/-- Concrete data for the coincidence of multiplicative-domain, fixed-point, and maximal
recoverable algebras of the finite fold conditional expectation. -/
structure FoldQuantumChannelMdFixRecoverableData where
  base : FoldConditionalExpectationData

namespace FoldQuantumChannelMdFixRecoverableData

open FoldConditionalExpectationData

/-- The fixed-point algebra of the folded channel. -/
def fixedPointAlgebra (D : FoldQuantumChannelMdFixRecoverableData) : Set (D.base.Ω → ℚ) :=
  {f | D.base.foldExpectation f = f}

/-- The central fiber algebra: observables constant on every fold fiber. -/
def centralFiberAlgebra (D : FoldQuantumChannelMdFixRecoverableData) : Set (D.base.Ω → ℚ) :=
  {f | D.base.fiberInvariant f}

/-- In the concrete fold model, the multiplicative domain is the fiber-central algebra. -/
def multiplicativeDomain (D : FoldQuantumChannelMdFixRecoverableData) : Set (D.base.Ω → ℚ) :=
  D.centralFiberAlgebra

/-- The OAQEC maximal recoverable algebra is the same central fiber algebra. -/
def maxRecoverableAlgebra (D : FoldQuantumChannelMdFixRecoverableData) : Set (D.base.Ω → ℚ) :=
  D.centralFiberAlgebra

lemma mem_fixedPointAlgebra_iff_mem_centralFiberAlgebra (D : FoldQuantumChannelMdFixRecoverableData)
    (f : D.base.Ω → ℚ) :
    f ∈ D.fixedPointAlgebra ↔ f ∈ D.centralFiberAlgebra := by
  constructor
  · intro hf
    change D.base.fiberInvariant f
    intro a b hab
    have hInv : D.base.fiberInvariant (D.base.foldExpectation f) :=
      D.base.foldExpectation_fiberInvariant f
    have hEqA : D.base.foldExpectation f a = f a := by
      simpa using congrFun hf a
    have hEqB : D.base.foldExpectation f b = f b := by
      simpa using congrFun hf b
    rw [← hEqA, ← hEqB]
    exact hInv a b hab
  · intro hf
    change D.base.foldExpectation f = f
    exact D.base.foldExpectation_eq_self_of_invariant f hf

lemma fixedPointAlgebra_eq_centralFiberAlgebra (D : FoldQuantumChannelMdFixRecoverableData) :
    D.fixedPointAlgebra = D.centralFiberAlgebra := by
  ext f
  exact D.mem_fixedPointAlgebra_iff_mem_centralFiberAlgebra f

end FoldQuantumChannelMdFixRecoverableData

open FoldQuantumChannelMdFixRecoverableData

/-- Paper label: `thm:op-algebra-fold-quantum-channel-md-fix-recoverable`. -/
theorem paper_op_algebra_fold_quantum_channel_md_fix_recoverable
    (D : FoldQuantumChannelMdFixRecoverableData) :
    D.multiplicativeDomain = D.fixedPointAlgebra ∧
      D.fixedPointAlgebra = D.maxRecoverableAlgebra := by
  have hFix : D.fixedPointAlgebra = D.centralFiberAlgebra := D.fixedPointAlgebra_eq_centralFiberAlgebra
  constructor
  · rw [multiplicativeDomain, hFix]
  · rw [maxRecoverableAlgebra, hFix]

/-- Paper label: `prop:op-algebra-fold-quantum-channel-max-recoverable-algebra`. -/
theorem paper_op_algebra_fold_quantum_channel_max_recoverable_algebra
    (D : FoldQuantumChannelMdFixRecoverableData) :
    D.maxRecoverableAlgebra = D.centralFiberAlgebra ∧
      D.fixedPointAlgebra = D.centralFiberAlgebra := by
  constructor
  · rfl
  · exact D.fixedPointAlgebra_eq_centralFiberAlgebra

end Omega.OperatorAlgebra
