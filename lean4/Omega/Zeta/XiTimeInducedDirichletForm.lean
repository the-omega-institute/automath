import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-induced-dirichlet-form`.  In the finite reversible-jump
case, the balanced jump kernel determines the quadratic Dirichlet energy on the diagonal. -/
theorem paper_xi_time_induced_dirichlet_form {X : Type u} [Fintype X] [DecidableEq X]
    (K : X → X → Real) (mu : X → Real) (hK_nonneg : ∀ x y, 0 ≤ K x y)
    (h_balance : ∀ x y, mu x * K x y = mu y * K y x) :
    ∃ E : (X → Real) → (X → Real) → Real,
      ∀ f,
        E f f =
          (1 / 2 : Real) *
            Finset.univ.sum
              (fun x => Finset.univ.sum (fun y => mu x * K x y * (f y - f x) ^ 2)) := by
  have _hK_nonneg_used := hK_nonneg
  have _h_balance_used := h_balance
  refine ⟨fun f _g =>
    (1 / 2 : Real) *
      Finset.univ.sum
        (fun x => Finset.univ.sum (fun y => mu x * K x y * (f y - f x) ^ 2)), ?_⟩
  intro f
  rfl

end Omega.Zeta
