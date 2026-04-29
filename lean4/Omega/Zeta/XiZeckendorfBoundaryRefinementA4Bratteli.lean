import Mathlib.Tactic
import Omega.Folding.StableSyntax

namespace Omega.Zeta

noncomputable instance xi_zeckendorf_boundary_refinement_a4_bratteli_fiber_fintype
    (m : Nat) (x : Omega.X m) :
    Fintype {y : Omega.X (m + 1) // Omega.X.restrict y = x} := by
  classical
  infer_instance

/-- Paper label: `thm:xi-zeckendorf-boundary-refinement-a4-bratteli`. -/
theorem paper_xi_zeckendorf_boundary_refinement_a4_bratteli (m : Nat) (hm : 1 ≤ m) :
    (∀ x : Omega.X m, Omega.X.EndsInZero x →
      Fintype.card {y : Omega.X (m + 1) // Omega.X.restrict y = x} = 2) ∧
    (∀ x : Omega.X m, Omega.X.EndsInOne x →
      Fintype.card {y : Omega.X (m + 1) // Omega.X.restrict y = x} = 1) := by
  classical
  have _hm : 1 ≤ m := hm
  constructor
  · intro x hx
    let e : {y : Omega.X (m + 1) // Omega.X.restrict y = x} ≃ Bool :=
      { toFun := fun y => Omega.last y.1.1
        invFun := fun b =>
        if b then
          ⟨Omega.X.appendTrue x hx, by simp [Omega.X.restrict_appendTrue]⟩
        else
          ⟨Omega.X.appendFalse x, by simp [Omega.X.restrict_appendFalse]⟩
        left_inv := by
          intro y
          rcases y with ⟨y, hy⟩
          dsimp at hy ⊢
          subst x
          apply Subtype.ext
          dsimp
          by_cases hlast : Omega.last y.1 = true
          · have hrestrict : Omega.X.EndsInZero (Omega.X.restrict y) := by
              simpa [Omega.X.EndsInZero, hlast] using
                Omega.X.restrict_endsInZero_of_last_true y hlast
            have hreconstruct :
                Omega.X.appendTrue (Omega.X.restrict y) hrestrict = y :=
              Omega.X.appendTrue_reconstruct y hlast hrestrict
            simp [hlast]
            exact hreconstruct
          · have hlastFalse : Omega.last y.1 = false := by
              cases h : Omega.last y.1
              · rfl
              · exact False.elim (hlast h)
            have hreconstruct :
                Omega.X.appendFalse (Omega.X.restrict y) = y :=
              Omega.X.appendFalse_reconstruct y hlastFalse
            simp [hlastFalse]
            exact hreconstruct
        right_inv := by
          intro b
          cases b <;> simp [Omega.X.appendFalse, Omega.X.appendTrue, Omega.last, Omega.snoc] }
    calc
      Fintype.card {y : Omega.X (m + 1) // Omega.X.restrict y = x}
          = Fintype.card Bool := Fintype.card_congr e
      _ = 2 := by simp
  · intro x hx
    let e : {y : Omega.X (m + 1) // Omega.X.restrict y = x} ≃ Unit :=
      { toFun := fun _ => ()
        invFun := fun _ => ⟨Omega.X.appendFalse x, by simp [Omega.X.restrict_appendFalse]⟩
        left_inv := by
          intro y
          rcases y with ⟨y, hy⟩
          dsimp at hy ⊢
          subst x
          apply Subtype.ext
          dsimp
          by_cases hlast : Omega.last y.1 = true
          · have hzero : Omega.X.EndsInZero (Omega.X.restrict y) :=
              Omega.X.restrict_endsInZero_of_last_true y hlast
            exact False.elim (Omega.X.endsInZero_not_endsInOne (Omega.X.restrict y) hzero hx)
          · have hlastFalse : Omega.last y.1 = false := by
              cases h : Omega.last y.1
              · rfl
              · exact False.elim (hlast h)
            have hreconstruct :
                Omega.X.appendFalse (Omega.X.restrict y) = y :=
              Omega.X.appendFalse_reconstruct y hlastFalse
            exact hreconstruct
        right_inv := by
          intro u
          cases u
          rfl }
    calc
      Fintype.card {y : Omega.X (m + 1) // Omega.X.restrict y = x}
          = Fintype.card Unit := Fintype.card_congr e
      _ = 1 := by simp

end Omega.Zeta
