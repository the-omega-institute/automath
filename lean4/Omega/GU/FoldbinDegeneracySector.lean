import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic

/-!
# Bin-fold degeneracy sector last-bit interval rigidity seed values

Fibonacci values, power-of-two cardinalities, and interval constraints.
-/

namespace Omega.GU

/-- Bin-fold degeneracy sector last-bit interval seeds.
    thm:gut-foldbin-degeneracy-sector-lastbit-interval -/
theorem paper_gut_foldbin_degeneracy_sector_lastbit_interval_seeds :
    (Nat.fib 8 = 21 ∧ Nat.fib 10 = 55) ∧
    (2 ^ 6 = 64) ∧
    (Nat.fib 4 = 3 ∧ Nat.fib 5 = 5) ∧
    (1 ≤ 2 ∧ 2 ≤ 3) ∧
    (Nat.fib 6 = 8 ∧ 16 / 8 = 2) := by
  refine ⟨⟨by native_decide, by native_decide⟩, by norm_num,
         ⟨by decide, by decide⟩, ⟨by omega, by omega⟩,
         ⟨by decide, by omega⟩⟩

/-- Paper wrapper: equal endpoint cardinalities in an antitone tail family force every
    intermediate tail cardinality to match the same value.
    thm:gut-foldbin-degeneracy-sector-lastbit-interval -/
theorem paper_gut_foldbin_degeneracy_sector_lastbit_interval {β : Type*} [DecidableEq β]
    (tail : Bool → ℕ → Finset β)
    (hanti : ∀ b v v', v ≤ v' → tail b v' ⊆ tail b v) :
    ∀ b v₁ v₂ v₃ d, v₁ ≤ v₂ → v₂ ≤ v₃ → (tail b v₁).card = d →
      (tail b v₃).card = d → (tail b v₂).card = d := by
  intro b v₁ v₂ v₃ d hv₁₂ hv₂₃ h₁ h₃
  have h₂₁ : tail b v₂ ⊆ tail b v₁ := hanti b v₁ v₂ hv₁₂
  have h₃₂ : tail b v₃ ⊆ tail b v₂ := hanti b v₂ v₃ hv₂₃
  have hle₂₁ : (tail b v₂).card ≤ (tail b v₁).card := Finset.card_le_card h₂₁
  have hle₃₂ : (tail b v₃).card ≤ (tail b v₂).card := Finset.card_le_card h₃₂
  omega

end Omega.GU
