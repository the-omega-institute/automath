import Mathlib.Tactic
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Data.Fintype.Card

namespace Omega.GU.SheetflipRegisterBound

/-- The number of non-identity involutions in S₃ is 3.
    prop:bdry-independent-sheetflip-register-lower-bound -/
theorem involutions_fin3 :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin 3) =>
      σ ≠ 1 ∧ σ * σ = 1)).card = 3 := by decide

/-- Cardinality of function space Fin n → Fin 3.
    prop:bdry-independent-sheetflip-register-lower-bound -/
theorem independent_choices_pow (n : ℕ) :
    Fintype.card (Fin n → Fin 3) = 3 ^ n := by
  simp [Fintype.card_fin]

/-- Register lower bound from injection existence.
    prop:bdry-independent-sheetflip-register-lower-bound -/
theorem register_lower_bound (n R : ℕ)
    (h : ∃ f : (Fin n → Fin 3) → Fin R, Function.Injective f) :
    3 ^ n ≤ R := by
  obtain ⟨f, hf⟩ := h
  have hcard := Fintype.card_le_of_injective f hf
  simp [Fintype.card_fin] at hcard
  exact hcard

/-- Paper label: `prop:bdry-independent-sheetflip-register-lower-bound`.
Any injective register encoding of the `3^n` independent sheet-flip choices needs at least `3^n`
register states. -/
theorem paper_bdry_independent_sheetflip_register_lower_bound {R : Type} [Fintype R] (n : Nat)
    (encode : (Fin n → Fin 3) → R) (hinj : Function.Injective encode) :
    3 ^ n <= Fintype.card R := by
  have hcard : Fintype.card (Fin n → Fin 3) <= Fintype.card R :=
    Fintype.card_le_of_injective encode hinj
  simpa [independent_choices_pow n] using hcard

/-- Paper seeds: sheetflip register bound concrete values.
    prop:bdry-independent-sheetflip-register-lower-bound -/
theorem paper_sheetflip_register_seeds :
    (Nat.fib 5 = 5 ∧ 3 ^ 5 = 243) ∧
    (Nat.fib 6 = 8 ∧ 3 ^ 8 = 6561) ∧
    (8 ≤ 3 ^ 5 ∧ 2 ^ 7 < 3 ^ 5) ∧
    (13 ≤ Nat.log 2 (3 ^ 8) + 1) := by
  refine ⟨⟨by native_decide, by norm_num⟩,
          ⟨by native_decide, by norm_num⟩,
          ⟨by norm_num, by norm_num⟩,
          by native_decide⟩

end Omega.GU.SheetflipRegisterBound
