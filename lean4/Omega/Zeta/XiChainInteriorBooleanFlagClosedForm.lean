import Mathlib

namespace Omega.Zeta

open Finset

/-- Boolean interval sign on subsets of `Fin m`. -/
def booleanIntervalSign {m : ℕ} (S T : Finset (Fin m)) : ℤ :=
  if S ⊆ T then (-1 : ℤ) ^ (T.card - S.card) else 0

/-- Concrete Boolean closed forms for the chain-interior model on the `n - 1` free coordinates. -/
def XiChainInteriorBooleanFlagClosedForm (n : ℕ) : Prop :=
  let m := n - 1
  Nonempty (Finset (Fin m) ≃ (Fin m → Bool)) ∧
    Fintype.card (Finset (Fin m)) = 2 ^ m ∧
    (∀ q : ℤ, ∑ S : Finset (Fin m), q ^ S.card = (q + 1) ^ m) ∧
    (∀ k : ℕ, Fintype.card (Fin m → Fin k) = k ^ m) ∧
    ∀ S T : Finset (Fin m), S ⊆ T → booleanIntervalSign S T = (-1 : ℤ) ^ (T.card - S.card)

theorem paper_xi_chain_interior_boolean_flag_closed_form (n : ℕ) :
    XiChainInteriorBooleanFlagClosedForm n := by
  classical
  let m := n - 1
  let φ : Finset (Fin m) ≃ (Fin m → Bool) :=
    { toFun := fun s i => if i ∈ s then true else false
      invFun := fun f => Finset.univ.filter fun i => f i
      left_inv := by
        intro s
        ext i
        by_cases hi : i ∈ s <;> simp [hi]
      right_inv := by
        intro f
        funext i
        by_cases hi : f i <;> simp [hi] }
  refine show
      Nonempty (Finset (Fin (n - 1)) ≃ (Fin (n - 1) → Bool)) ∧
        Fintype.card (Finset (Fin (n - 1))) = 2 ^ (n - 1) ∧
        (∀ q : ℤ, ∑ S : Finset (Fin (n - 1)), q ^ S.card = (q + 1) ^ (n - 1)) ∧
        (∀ k : ℕ, Fintype.card (Fin (n - 1) → Fin k) = k ^ (n - 1)) ∧
        ∀ S T : Finset (Fin (n - 1)),
          S ⊆ T → booleanIntervalSign S T = (-1 : ℤ) ^ (T.card - S.card) from ?_
  refine ⟨by simpa [m] using (show Nonempty (Finset (Fin m) ≃ (Fin m → Bool)) from ⟨φ⟩), ?_, ?_, ?_, ?_⟩
  · simpa [m] using (Fintype.card_finset (α := Fin m))
  · intro q
    have h₁ :
        (∑ S : Finset (Fin m), q ^ S.card) =
          Finset.sum ((Finset.univ : Finset (Fin m)).powerset) (fun S => q ^ S.card) := by
      simp
    have h₂ :
        Finset.sum ((Finset.univ : Finset (Fin m)).powerset) (fun S => q ^ S.card) =
          Finset.sum (Finset.range (m + 1)) (fun j => (m.choose j : ℤ) * q ^ j) := by
      simpa [nsmul_eq_mul, Finset.card_univ, m, mul_comm, mul_left_comm, mul_assoc] using
        (Finset.sum_powerset_apply_card (α := ℤ) (β := Fin m) (f := fun t : ℕ => q ^ t)
          (x := (Finset.univ : Finset (Fin m))))
    have h₃ :
        Finset.sum (Finset.range (m + 1)) (fun j => (m.choose j : ℤ) * q ^ j) = (q + 1) ^ m := by
      simpa [one_pow, mul_one, mul_comm, mul_left_comm, mul_assoc, add_comm] using
        (add_pow q 1 m).symm
    exact h₁.trans (h₂.trans h₃)
  · intro k
    simpa [m] using (Fintype.card_fun (α := Fin m) (β := Fin k))
  · intro S T hST
    simpa [m] using (show booleanIntervalSign S T = (-1 : ℤ) ^ (T.card - S.card) by
      simp [booleanIntervalSign, hST])

end Omega.Zeta
