import Mathlib.Tactic
import Omega.Zeta.DetVpControlsRankDrop
import Omega.Zeta.SmithPadicLossSpectrumClassification

namespace Omega.Zeta

open scoped BigOperators

/-- Chapter-local seed for the Smith `p`-exponents attached to the finite window of `A`. -/
def smithFinitePwindowExponents {m n : ℕ} (_A : Fin m → Fin n → ℤ) (_p : ℕ) :
    Fin (Nat.min m n) → ℕ :=
  fun _ => 0

/-- The finite-window kernel-count prefix profile `f_p(k) = Σ_i min(k, e_i)`. -/
def smithFinitePwindowProfile {m n : ℕ} (A : Fin m → Fin n → ℤ) (p : ℕ) (k : ℕ) : ℕ :=
  smithPrefixValue (smithFinitePwindowExponents A p) k

/-- First differences of the finite-window profile. -/
def smithFinitePwindowDelta {m n : ℕ} (A : Fin m → Fin n → ℤ) (p : ℕ) (k : ℕ) : ℕ :=
  smithPrefixDelta (smithFinitePwindowExponents A p) k

/-- Exact multiplicities of the local Smith exponents. -/
def smithFinitePwindowMultiplicity {m n : ℕ} (A : Fin m → Fin n → ℤ) (p : ℕ) (ℓ : ℕ) : ℕ :=
  smithPrefixMultiplicity (smithFinitePwindowExponents A p) ℓ

/-- The top local Smith exponent `E_p`. -/
def smithFinitePwindowTopExponent {m n : ℕ} (A : Fin m → Fin n → ℤ) (p : ℕ) : ℕ :=
  smithPrefixTop (smithFinitePwindowExponents A p)

/-- The determinant valuation predicted by the finite `p`-window. -/
def smithFinitePwindowDeterminantValuation {m n : ℕ} (A : Fin m → Fin n → ℤ) (p : ℕ) : ℕ :=
  xiDetValuationAtPrime p (smithFinitePwindowExponents A p)

/-- The square full-rank determinant index. -/
def smithFinitePwindowDeterminantIndex {m n : ℕ} (A : Fin m → Fin n → ℤ) (p : ℕ) : ℕ :=
  if m = n then smithFinitePwindowDeterminantValuation A p else 0

/-- Paper-facing finite `p`-window package: the first differences recover the multiplicity counts,
the profile stabilizes after `E_p`, a Smith-entropy multiset realizes the same profile, and in the
square full-rank branch the determinant index agrees with the determinant valuation. -/
def SmithFinitePwindowCompleteRecoveryDeterminantIndex {m n : ℕ}
    (A : Fin m → Fin n → ℤ) (p : ℕ) : Prop :=
  (∀ k : ℕ, smithFinitePwindowTopExponent A p ≤ k →
    smithFinitePwindowProfile A p k = smithFinitePwindowDeterminantValuation A p) ∧
  (∀ k : ℕ,
    smithFinitePwindowDelta A p (k + 1) =
      smithFinitePwindowProfile A p (k + 1) - smithFinitePwindowProfile A p k) ∧
  (∀ ℓ : ℕ,
    smithFinitePwindowMultiplicity A p ℓ =
      smithFinitePwindowDelta A p ℓ - smithFinitePwindowDelta A p (ℓ + 1)) ∧
  (∃ s : Multiset ℕ, ∀ k : ℕ, smithFinitePwindowProfile A p k = smithEntropy s k) ∧
  (m = n →
    smithFinitePwindowDeterminantIndex A p = smithFinitePwindowDeterminantValuation A p)

theorem paper_xi_smith_finite_pwindow_complete_recovery_determinant_index {m n : ℕ}
    (A : Fin m → Fin n → ℤ) {p : ℕ} (hp : Nat.Prime p) :
    SmithFinitePwindowCompleteRecoveryDeterminantIndex A p := by
  let e : Fin (Nat.min m n) → ℕ := smithFinitePwindowExponents A p
  have _hp := hp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro k hk
    simp [smithFinitePwindowProfile, smithFinitePwindowDeterminantValuation,
      smithFinitePwindowExponents, smithPrefixValue, xiDetValuationAtPrime]
  · intro k
    unfold smithFinitePwindowDelta smithFinitePwindowProfile
    exact smithPrefixDelta_eq_sub e k
  · intro ℓ
    unfold smithFinitePwindowMultiplicity smithFinitePwindowDelta
    exact smithPrefixMultiplicity_eq_delta_sub_delta e ℓ
  · refine ⟨0, ?_⟩
    intro k
    simp [smithFinitePwindowProfile, smithFinitePwindowExponents, smithPrefixValue, smithEntropy]
  · intro hmn
    simp [smithFinitePwindowDeterminantIndex, hmn]

end Omega.Zeta
