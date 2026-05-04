import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part55ba-terminal-sector-order-ideal`. -/
theorem paper_xi_time_part55ba_terminal_sector_order_ideal
    (m : ℕ) (τ : Bool) (X F : Type*) [Fintype X] [Fintype F]
    (terminal : X → Bool) (V d : X → ℕ) (W : F → ℕ)
    (hsector : ∀ x : X, terminal x = τ)
    (hd : ∀ x : X, d x = Fintype.card {c : F // W c ≤ 2 ^ m - 1 - V x}) :
    (∀ x y : X, V x = V y → d x = d y) ∧
      (∀ x y : X, V x ≤ V y → d y ≤ d x) ∧
      (∀ r : ℕ, 1 ≤ r → ∀ x y : X, r ≤ d y → V x ≤ V y → r ≤ d x) := by
  classical
  have _ : ∀ x : X, terminal x = τ := hsector
  have hmono :
      ∀ x y : X, V x ≤ V y → d y ≤ d x := by
    intro x y hV
    have hthreshold : 2 ^ m - 1 - V y ≤ 2 ^ m - 1 - V x :=
      Nat.sub_le_sub_left hV (2 ^ m - 1)
    rw [hd y, hd x]
    refine Fintype.card_le_of_injective
      (fun c : {c : F // W c ≤ 2 ^ m - 1 - V y} =>
        (⟨c.1, le_trans c.2 hthreshold⟩ :
          {c : F // W c ≤ 2 ^ m - 1 - V x}))
      ?_
    intro a b hab
    exact Subtype.ext
      (congrArg (fun z : {c : F // W c ≤ 2 ^ m - 1 - V x} => z.1) hab)
  refine ⟨?_, hmono, ?_⟩
  · intro x y hV
    calc
      d x = Fintype.card {c : F // W c ≤ 2 ^ m - 1 - V x} := hd x
      _ = Fintype.card {c : F // W c ≤ 2 ^ m - 1 - V y} := by rw [hV]
      _ = d y := (hd y).symm
  · intro r _hr x y hry hV
    exact le_trans hry (hmono x y hV)

end Omega.Zeta
