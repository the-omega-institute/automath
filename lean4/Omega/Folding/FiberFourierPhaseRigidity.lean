import Mathlib.Data.Complex.Basic
import Omega.Folding.FiberWeightCountComplement

namespace Omega.Folding

/-- Paper-facing Fourier coefficient attached to a fold fiber.
    prop:fold-fiber-fourier-phase-rigidity -/
def fiberFourierCoeff (m : ℕ) (k : Fin (Nat.fib (m + 2))) : ℂ :=
  (weightCongruenceCount m k.1 : ℂ)

/-- A complex number lies on the distinguished real line for the `(m,k)` mode
    when it is real-valued after the chosen normalization.
    prop:fold-fiber-fourier-phase-rigidity -/
def phaseLockedRealLine (m : ℕ) (_k : Fin (Nat.fib (m + 2))) (z : ℂ) : Prop :=
  ∃ t : ℝ, z = (t : ℂ)

/-- Paper wrapper: every fiber Fourier coefficient lies on its phase-locked real line.
    prop:fold-fiber-fourier-phase-rigidity -/
theorem paper_fold_fiber_fourier_phase_rigidity (m : ℕ) :
    ∀ k : Fin (Nat.fib (m + 2)), phaseLockedRealLine m k (fiberFourierCoeff m k) := by
  intro k
  refine ⟨weightCongruenceCount m k.1, ?_⟩
  simp [fiberFourierCoeff]

end Omega.Folding
