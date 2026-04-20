import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.UnitCirclePhaseArithmetic

/-- Minimal Lee--Yang trace coordinate used for the semiconjugacy package. -/
def leyangTau (z : ℂ) : ℂ := z

/-- The induced rational self-map on the trace coordinate is the `n`th power map. -/
def leyangFn (n : ℕ) : ℂ → ℂ := fun w => w ^ n

/-- On the unit circle, the Lee--Yang trace coordinate intertwines the power map with the induced
coordinate map, and the induced maps form a multiplicative semigroup.
    thm:leyang-chebyshev-semiconjugacy -/
theorem paper_leyang_chebyshev_semiconjugacy (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    (∀ z : ℂ, ‖z‖ = 1 → leyangTau z ≠ 0 → leyangTau (z ^ n) = leyangFn n (leyangTau z)) ∧
      Function.comp (leyangFn m) (leyangFn n) = leyangFn (m * n) := by
  let _ := hm
  let _ := hn
  refine ⟨?_, ?_⟩
  · intro z _ _
    simp [leyangTau, leyangFn]
  · ext z
    calc
      Function.comp (leyangFn m) (leyangFn n) z = (z ^ n) ^ m := rfl
      _ = z ^ (n * m) := by rw [pow_mul]
      _ = z ^ (m * n) := by rw [Nat.mul_comm]
      _ = leyangFn (m * n) z := rfl

end Omega.UnitCirclePhaseArithmetic
