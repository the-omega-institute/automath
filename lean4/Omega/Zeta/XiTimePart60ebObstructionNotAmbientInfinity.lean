import Mathlib.Tactic

namespace Omega.Zeta

/-- A uniform finite Toeplitz truncation certificate for a bounded realization class. -/
def xi_time_part60eb_obstruction_not_ambient_infinity_finite_truncation
    {Obj : Type*} (toeplitzPositive : Obj → ℕ → Prop) (N0 : ℕ) : Prop :=
  ∀ X : Obj, (∀ N, toeplitzPositive X N) ↔ ∀ N, N ≤ N0 → toeplitzPositive X N

/-- The two structural mechanisms singled out by the no-go: unbounded realization dimension and
visible collapse of distinct prime-ledger kernel states. -/
def xi_time_part60eb_obstruction_not_ambient_infinity_structural_obstruction
    {Obj Kernel Visible : Type*} (realizationDim : Obj → ℕ) (visible : Kernel → Visible)
    (kernelTruth : Kernel → Prop) : Prop :=
  (∀ D, ∃ X : Obj, D < realizationDim X) ∧
    ∃ k1 k2 : Kernel, visible k1 = visible k2 ∧ kernelTruth k1 ∧ ¬ kernelTruth k2

/-- Paper label: `prop:xi-time-part60eb-obstruction-not-ambient-infinity`.

With a uniform realization-dimension bound, choosing `N0 = 2 * D` gives a finite
Toeplitz certificate. Consequently the no-go package, when present, decomposes into the separate
unbounded-dimension and visible-kernel-distortion mechanisms rather than ambient infinitude alone. -/
theorem paper_xi_time_part60eb_obstruction_not_ambient_infinity
    {Obj Kernel Visible : Type*} (realizationDim : Obj → ℕ)
    (toeplitzPositive : Obj → ℕ → Prop) (visible : Kernel → Visible)
    (kernelTruth : Kernel → Prop) (D : ℕ)
    (hBounded : ∀ X : Obj, realizationDim X ≤ D)
    (hThreshold : ∀ X : Obj, ∀ N0,
      2 * realizationDim X ≤ N0 →
        ((∀ N, toeplitzPositive X N) ↔ ∀ N, N ≤ N0 → toeplitzPositive X N)) :
    (∃ N0,
      N0 ≤ 2 * D ∧
        xi_time_part60eb_obstruction_not_ambient_infinity_finite_truncation
          toeplitzPositive N0) ∧
      (xi_time_part60eb_obstruction_not_ambient_infinity_structural_obstruction
          realizationDim visible kernelTruth →
        (∀ D, ∃ X : Obj, D < realizationDim X) ∧
          ∃ k1 k2 : Kernel, visible k1 = visible k2 ∧ kernelTruth k1 ∧ ¬ kernelTruth k2) := by
  refine ⟨?_, ?_⟩
  · refine ⟨2 * D, le_rfl, ?_⟩
    intro X
    exact hThreshold X (2 * D) (Nat.mul_le_mul_left 2 (hBounded X))
  · intro h
    exact h

end Omega.Zeta
