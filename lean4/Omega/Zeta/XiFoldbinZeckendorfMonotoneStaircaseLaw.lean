import Mathlib.Tactic

theorem paper_xi_foldbin_zeckendorf_monotone_staircase_law
    {Word : Type} (last : Word -> Bool) (V d : Word -> Nat) (D : Bool -> Nat -> Nat)
    (hrepr : ∀ w, d w = D (last w) (V w))
    (hmono : ∀ e x y, x ≤ y -> D e y ≤ D e x) :
    ∃ N : Bool -> Nat -> Nat,
      (∀ w, d w = N (last w) (V w)) ∧
        (∀ e x y, x ≤ y -> N e y ≤ N e x) := by
  refine ⟨D, ?_, ?_⟩
  · exact hrepr
  · exact hmono
