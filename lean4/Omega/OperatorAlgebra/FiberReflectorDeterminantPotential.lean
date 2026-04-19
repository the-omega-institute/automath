import Mathlib.Tactic
import Omega.Folding.FiberArithmetic
import Omega.POM.KernelSpectrum

namespace Omega.OperatorAlgebra

/-- Spectral product for the determinant potential of the fiber reflector `K_m`: the `1`-eigenspace
contributes `(1 + t)^{|X_m|}` and the `0`-eigenspace contributes `1^{2^m - |X_m|}`. -/
noncomputable def fiberReflectorDeterminantPotential (m : Nat) (t : ℝ) : ℝ :=
  (1 + t) ^ Fintype.card (Omega.X m) * 1 ^ (2 ^ m - Fintype.card (Omega.X m))

/-- The normalized logarithmic determinant potential attached to the reflector spectrum. -/
noncomputable def fiberReflectorNormalizedLogPotential (m : Nat) (t : ℝ) : ℝ :=
  (1 / (m : ℝ)) * Real.log (fiberReflectorDeterminantPotential m t)

/-- Paper-facing determinant-potential formula for the fiber reflector: after separating the
`1`- and `0`-eigenspaces, the determinant is `(1 + t)^{|X_m|}` and the normalized logarithm is
`(|X_m| / m) log (1 + t)`, equivalently `F_{m+2} / m · log (1 + t)`.
    cor:op-algebra-fiber-reflector-determinant-potential -/
theorem paper_op_algebra_fiber_reflector_determinant_potential (m : Nat) (t : ℝ) :
    fiberReflectorDeterminantPotential m t = (1 + t) ^ Fintype.card (Omega.X m) ∧
      fiberReflectorDeterminantPotential m t = (1 + t) ^ Nat.fib (m + 2) ∧
      fiberReflectorNormalizedLogPotential m t =
        ((Fintype.card (Omega.X m) : ℝ) / m) * Real.log (1 + t) ∧
      fiberReflectorNormalizedLogPotential m t =
        ((Nat.fib (m + 2) : ℝ) / m) * Real.log (1 + t) := by
  have hdet :
      fiberReflectorDeterminantPotential m t = (1 + t) ^ Fintype.card (Omega.X m) := by
    simp [fiberReflectorDeterminantPotential]
  have hlog :
      fiberReflectorNormalizedLogPotential m t =
        ((Fintype.card (Omega.X m) : ℝ) / m) * Real.log (1 + t) := by
    unfold fiberReflectorNormalizedLogPotential
    rw [hdet, Real.log_pow]
    ring
  refine ⟨hdet, ?_, hlog, ?_⟩
  · rw [hdet, Omega.X.card_eq_fib]
  · rw [hlog, Omega.X.card_eq_fib]

end Omega.OperatorAlgebra
