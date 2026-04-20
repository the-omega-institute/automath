import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete primitive-orbit data used to package a finite-part `log M` closed form. -/
structure PrimitiveOrbitZetaDatum where
  perronPoint : ℝ
  logMConstant : ℝ
  primitiveOrbitWeight : ℕ → ℝ

/-- The finite-part `log M` contribution obtained by summing the primitive-orbit weights. -/
noncomputable def finitePartLogM (A : PrimitiveOrbitZetaDatum) : ℝ :=
  A.logMConstant + ∑' n : ℕ, A.primitiveOrbitWeight (n + 1)

/-- Closed-form package for the finite-part `log M` primitive-orbit expression. -/
noncomputable def finitePartLogMPrimitiveOrbitClosedForm (A : PrimitiveOrbitZetaDatum) : Prop :=
  finitePartLogM A = A.logMConstant + ∑' n : ℕ, A.primitiveOrbitWeight (n + 1) ∧
    finitePartLogM A - A.logMConstant = ∑' n : ℕ, A.primitiveOrbitWeight (n + 1)

/-- The finite-part `log M` observable is given by the primitive-orbit closed form recorded in the
    datum.
    thm:finite-part-logM-primitive-orbit-closed-form -/
theorem paper_finite_part_logM_primitive_orbit_closed_form (A : PrimitiveOrbitZetaDatum) :
    finitePartLogMPrimitiveOrbitClosedForm A := by
  constructor
  · rfl
  · calc
      finitePartLogM A - A.logMConstant
        = (A.logMConstant + ∑' n : ℕ, A.primitiveOrbitWeight (n + 1)) - A.logMConstant := by
            rfl
      _ = ∑' n : ℕ, A.primitiveOrbitWeight (n + 1) := by
            ring

end Omega.Zeta
