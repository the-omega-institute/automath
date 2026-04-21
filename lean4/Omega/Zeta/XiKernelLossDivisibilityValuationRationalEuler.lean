import Mathlib.Tactic
import Omega.Zeta.SmithPrefixSufficiency

namespace Omega.Zeta

open scoped BigOperators

/-- Lean-side package for the primewise Smith-kernel loss profile: the local valuation is modular
with respect to `max/min`, the tail stabilizes at the top Smith exponent, and the discrete
derivative recovers the exponent multiplicities. -/
def XiKernelLossDivisibilityValuationRationalEulerLaw : Prop :=
  (∀ {m : ℕ} (e : Fin m → ℕ) (u v : ℕ),
    smithPrefixValue e (max u v) + smithPrefixValue e (min u v) =
      smithPrefixValue e u + smithPrefixValue e v) ∧
  (∀ {m : ℕ} (e : Fin m → ℕ) (k : ℕ),
    smithPrefixTop e ≤ k → smithPrefixValue e k = ∑ i, e i) ∧
  (∀ {m : ℕ} (e : Fin m → ℕ) (ℓ : ℕ),
    smithPrefixMultiplicity e ℓ =
      smithPrefixDelta e ℓ - smithPrefixDelta e (ℓ + 1))

/-- Paper label: `thm:xi-kernel-loss-divisibility-valuation-rational-euler`.
The Smith-prefix profile is the primewise kernel-loss valuation on the divisibility lattice; its
eventual plateau is the ingredient behind the rational Euler tail, and the first differences
recover the exact Smith exponent multiplicities. -/
theorem paper_xi_kernel_loss_divisibility_valuation_rational_euler :
    XiKernelLossDivisibilityValuationRationalEulerLaw := by
  refine ⟨?_, ?_, ?_⟩
  · intro m e u v
    by_cases huv : u ≤ v
    · simp [Nat.max_eq_right huv, Nat.min_eq_left huv, add_comm]
    · have hvu : v ≤ u := le_of_not_ge huv
      simp [Nat.max_eq_left hvu, Nat.min_eq_right hvu]
  · intro m e k hk
    exact smithPrefixValue_eq_total_of_le_top e k hk
  · intro m e ℓ
    exact smithPrefixMultiplicity_eq_delta_sub_delta e ℓ

end Omega.Zeta
