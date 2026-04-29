import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete data for
`prop:conclusion-fibadic-saturated-observer-cofinality`.  The record keeps the
exact-depth Fibonacci conductor saturation, together with the minimal-resolution
divisibility package used to compare any other resolving depth with `depth N`. -/
structure conclusion_fibadic_saturated_observer_cofinality_data where
  depth : ℕ → ℕ
  fibonacciConductor : ℕ → ℕ
  depth_pos : ∀ N : ℕ, 0 < N → 0 < depth N
  exactDepthConductorSaturation : ∀ N : ℕ, 0 < N → N ∣ fibonacciConductor (depth N)
  minimalResolutionDivides :
    ∀ N e : ℕ, 0 < N → N ∣ fibonacciConductor e → 0 < e → depth N ∣ e

namespace conclusion_fibadic_saturated_observer_cofinality_data

/-- The reduction map modulo the observed conductor. -/
def conclusion_fibadic_saturated_observer_cofinality_quotientMap
    (N : ℕ) (hN : 0 < N) : ℕ → Fin N :=
  fun a => ⟨a % N, Nat.mod_lt a hN⟩

/-- A natural surjection at depth `e` is encoded by conductor divisibility and a
positive resolving depth. -/
def hasNaturalSurjection
    (D : conclusion_fibadic_saturated_observer_cofinality_data) (N e : ℕ) : Prop :=
  N ∣ D.fibonacciConductor e ∧ 0 < e

end conclusion_fibadic_saturated_observer_cofinality_data

open conclusion_fibadic_saturated_observer_cofinality_data

/-- Paper label: `prop:conclusion-fibadic-saturated-observer-cofinality`. -/
theorem paper_conclusion_fibadic_saturated_observer_cofinality
    (D : conclusion_fibadic_saturated_observer_cofinality_data) (N : ℕ) (hN : 0 < N) :
    D.hasNaturalSurjection N (D.depth N) ∧
      ∀ e, D.hasNaturalSurjection N e → D.depth N ≤ e := by
  constructor
  · exact ⟨D.exactDepthConductorSaturation N hN, D.depth_pos N hN⟩
  · intro e he
    rcases he with ⟨hdivN, hepos⟩
    rcases D.minimalResolutionDivides N e hN hdivN hepos with ⟨q, rfl⟩
    have hqpos : 0 < q := by
      by_contra hq
      have hqzero : q = 0 := Nat.eq_zero_of_not_pos hq
      subst q
      simp at hepos
    have hq : 1 ≤ q := Nat.succ_le_of_lt hqpos
    simpa using Nat.mul_le_mul_left (D.depth N) hq

end Omega.Conclusion
