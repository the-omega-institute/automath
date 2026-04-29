import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- The finite volume split into the `d = 2`, `d = 3`, and `d = 4` window-`6` sites. -/
structure conclusion_window6_hidden_averaging_zero_budget_data where
  LambdaTwo : Type
  LambdaThree : Type
  LambdaFour : Type
  [fintypeTwo : Fintype LambdaTwo]
  [fintypeThree : Fintype LambdaThree]
  [fintypeFour : Fintype LambdaFour]

attribute [instance] conclusion_window6_hidden_averaging_zero_budget_data.fintypeTwo
attribute [instance] conclusion_window6_hidden_averaging_zero_budget_data.fintypeThree
attribute [instance] conclusion_window6_hidden_averaging_zero_budget_data.fintypeFour

/-- The index type `Λ`, partitioned by local fiber dimension. -/
abbrev conclusion_window6_hidden_averaging_zero_budget_index
    (D : conclusion_window6_hidden_averaging_zero_budget_data) :=
  Sum D.LambdaTwo (Sum D.LambdaThree D.LambdaFour)

/-- Local complement sizes after removing exact hidden-averaging zero residues:
`d=2` removes two residues, `d=3` removes none, and `d=4` removes three. -/
def conclusion_window6_hidden_averaging_zero_budget_local_complement
    {D : conclusion_window6_hidden_averaging_zero_budget_data}
    (x : conclusion_window6_hidden_averaging_zero_budget_index D) : ℕ :=
  match x with
  | .inl _ => 62
  | .inr (.inl _) => 64
  | .inr (.inr _) => 61

/-- Complement assignments, with each coordinate ranging over its allowed residues. -/
abbrev conclusion_window6_hidden_averaging_zero_budget_complement_assignments
    (D : conclusion_window6_hidden_averaging_zero_budget_data) :=
  ∀ x : conclusion_window6_hidden_averaging_zero_budget_index D,
    Fin (conclusion_window6_hidden_averaging_zero_budget_local_complement x)

/-- Product decomposition of the independent coordinate complement. -/
def conclusion_window6_hidden_averaging_zero_budget_complement_equiv
    (D : conclusion_window6_hidden_averaging_zero_budget_data) :
    conclusion_window6_hidden_averaging_zero_budget_complement_assignments D ≃
      ((D.LambdaTwo → Fin 62) × (D.LambdaThree → Fin 64) × (D.LambdaFour → Fin 61)) where
  toFun f := (fun x => f (.inl x), fun x => f (.inr (.inl x)), fun x => f (.inr (.inr x)))
  invFun f
    | .inl x => f.1 x
    | .inr (.inl x) => f.2.1 x
    | .inr (.inr x) => f.2.2 x
  left_inv f := by
    funext x
    rcases x with x | x
    · rfl
    · rcases x with x | x <;> rfl
  right_inv f := by
    rcases f with ⟨f₂, f₃, f₄⟩
    rfl

/-- The product side of the complement decomposition is finite. -/
noncomputable instance conclusion_window6_hidden_averaging_zero_budget_product_fintype
    (D : conclusion_window6_hidden_averaging_zero_budget_data) :
    Fintype
      ((D.LambdaTwo → Fin 62) × (D.LambdaThree → Fin 64) × (D.LambdaFour → Fin 61)) := by
  classical
  infer_instance

/-- The dependent complement-assignment space is finite through its product decomposition. -/
noncomputable instance
    conclusion_window6_hidden_averaging_zero_budget_complement_assignments_fintype
    (D : conclusion_window6_hidden_averaging_zero_budget_data) :
    Fintype (conclusion_window6_hidden_averaging_zero_budget_complement_assignments D) :=
  Fintype.ofEquiv
    ((D.LambdaTwo → Fin 62) × (D.LambdaThree → Fin 64) × (D.LambdaFour → Fin 61))
    (conclusion_window6_hidden_averaging_zero_budget_complement_equiv D).symm

/-- The number of `d = 2` sites. -/
def conclusion_window6_hidden_averaging_zero_budget_N2
    (D : conclusion_window6_hidden_averaging_zero_budget_data) : ℕ :=
  Fintype.card D.LambdaTwo

/-- The number of `d = 3` sites. -/
def conclusion_window6_hidden_averaging_zero_budget_N3
    (D : conclusion_window6_hidden_averaging_zero_budget_data) : ℕ :=
  Fintype.card D.LambdaThree

/-- The number of `d = 4` sites. -/
def conclusion_window6_hidden_averaging_zero_budget_N4
    (D : conclusion_window6_hidden_averaging_zero_budget_data) : ℕ :=
  Fintype.card D.LambdaFour

/-- The total number of Fourier residue assignments. -/
def conclusion_window6_hidden_averaging_zero_budget_total
    (D : conclusion_window6_hidden_averaging_zero_budget_data) : ℕ :=
  64 ^ (conclusion_window6_hidden_averaging_zero_budget_N2 D +
    conclusion_window6_hidden_averaging_zero_budget_N3 D +
    conclusion_window6_hidden_averaging_zero_budget_N4 D)

/-- The closed form for the complement of the zero-mode union. -/
def conclusion_window6_hidden_averaging_zero_budget_complement_count
    (D : conclusion_window6_hidden_averaging_zero_budget_data) : ℕ :=
  62 ^ conclusion_window6_hidden_averaging_zero_budget_N2 D *
    64 ^ conclusion_window6_hidden_averaging_zero_budget_N3 D *
      61 ^ conclusion_window6_hidden_averaging_zero_budget_N4 D

/-- The zero-mode count obtained by subtracting the independent coordinate complement. -/
def conclusion_window6_hidden_averaging_zero_budget_zero_count
    (D : conclusion_window6_hidden_averaging_zero_budget_data) : ℕ :=
  conclusion_window6_hidden_averaging_zero_budget_total D -
    conclusion_window6_hidden_averaging_zero_budget_complement_count D

/-- The normalized zero-mode ratio in the paper's reduced algebraic form. -/
def conclusion_window6_hidden_averaging_zero_budget_ratio
    (D : conclusion_window6_hidden_averaging_zero_budget_data) : ℚ :=
  1 - ((31 : ℚ) / 32) ^ conclusion_window6_hidden_averaging_zero_budget_N2 D *
    ((61 : ℚ) / 64) ^ conclusion_window6_hidden_averaging_zero_budget_N4 D

namespace conclusion_window6_hidden_averaging_zero_budget_data

/-- Concrete statement for the window-`6` hidden averaging zero-budget formula. -/
def statement (D : conclusion_window6_hidden_averaging_zero_budget_data) : Prop :=
  Fintype.card (conclusion_window6_hidden_averaging_zero_budget_complement_assignments D) =
      conclusion_window6_hidden_averaging_zero_budget_complement_count D ∧
    conclusion_window6_hidden_averaging_zero_budget_zero_count D =
      conclusion_window6_hidden_averaging_zero_budget_total D -
        conclusion_window6_hidden_averaging_zero_budget_complement_count D ∧
    conclusion_window6_hidden_averaging_zero_budget_ratio D =
      1 - ((31 : ℚ) / 32) ^ conclusion_window6_hidden_averaging_zero_budget_N2 D *
        ((61 : ℚ) / 64) ^ conclusion_window6_hidden_averaging_zero_budget_N4 D

end conclusion_window6_hidden_averaging_zero_budget_data

/-- Paper label: `thm:conclusion-window6-hidden-averaging-zero-budget`. -/
theorem paper_conclusion_window6_hidden_averaging_zero_budget
    (D : conclusion_window6_hidden_averaging_zero_budget_data) : D.statement := by
  classical
  refine ⟨?_, rfl, rfl⟩
  have hcard :=
    Fintype.card_congr
      (conclusion_window6_hidden_averaging_zero_budget_complement_equiv D)
  simpa [conclusion_window6_hidden_averaging_zero_budget_complement_count,
    conclusion_window6_hidden_averaging_zero_budget_N2,
    conclusion_window6_hidden_averaging_zero_budget_N3,
    conclusion_window6_hidden_averaging_zero_budget_N4,
    Fintype.card_fun, Nat.mul_assoc] using hcard

end Omega.Conclusion
