import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-smith-local-euler-complete-invariant`. -/
theorem paper_xi_smith_local_euler_complete_invariant {Prime Matrix SmithInvariant : Type*}
    (localEulerCoeff : Matrix → Prime → ℕ → ℕ) (localLoss : Matrix → Prime → ℕ → ℤ)
    (smithNormalForm : Matrix → SmithInvariant)
    (recoverSmith : (Prime → ℕ → ℤ) → SmithInvariant)
    (coeffDeterminesLoss :
      ∀ A B,
        (∀ p k, localEulerCoeff A p k = localEulerCoeff B p k) →
          ∀ p k, localLoss A p k = localLoss B p k)
    (smithRecovered : ∀ A, smithNormalForm A = recoverSmith (localLoss A)) {A B : Matrix}
    (hEuler : ∀ p k, localEulerCoeff A p k = localEulerCoeff B p k) :
    smithNormalForm A = smithNormalForm B := by
  rw [smithRecovered A, smithRecovered B]
  congr 1
  funext p k
  exact coeffDeterminesLoss A B hEuler p k

end Omega.Zeta
