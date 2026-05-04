import Mathlib.Data.Fintype.EquivFin

/-- Splitting natural-valued coordinates on a finite direct sum, and identifying a
three-point boundary with `Fin 3`. -/
theorem paper_conclusion_window6_boundary_k0_positive_cone_face {Cyc Bd : Type*}
    [Fintype Cyc] [Fintype Bd] (hBd : Fintype.card Bd = 3) :
    Nonempty ((Sum Cyc Bd → ℕ) ≃ ((Cyc → ℕ) × (Bd → ℕ))) ∧
      Nonempty ((Bd → ℕ) ≃ (Fin 3 → ℕ)) := by
  classical
  constructor
  · exact ⟨
      { toFun := fun f => (fun c => f (Sum.inl c), fun b => f (Sum.inr b))
        invFun := fun p => Sum.elim p.1 p.2
        left_inv := by
          intro f
          funext x
          cases x <;> rfl
        right_inv := by
          intro p
          cases p
          rfl }⟩
  · let e : Bd ≃ Fin 3 := (Fintype.equivFin Bd).trans (Equiv.cast (by rw [hBd]))
    exact ⟨
      { toFun := fun f i => f (e.symm i)
        invFun := fun g b => g (e b)
        left_inv := by
          intro f
          funext b
          exact congrArg f (e.symm_apply_apply b)
        right_inv := by
          intro g
          funext i
          exact congrArg g (e.apply_symm_apply i) }⟩
