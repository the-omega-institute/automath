import Mathlib.Tactic

namespace Omega.Conclusion

universe u

/-- Label-prefixed concrete `Z₂`-torsor core: a type equipped with the nontrivial involution used
for the diagonal action on the square. -/
structure conclusion_z2torsor_square_parity_collapse_z2_torsor where
  conclusion_z2torsor_square_parity_collapse_carrier : Type u
  conclusion_z2torsor_square_parity_collapse_decidable_eq :
    DecidableEq conclusion_z2torsor_square_parity_collapse_carrier
  conclusion_z2torsor_square_parity_collapse_flip :
    conclusion_z2torsor_square_parity_collapse_carrier →
      conclusion_z2torsor_square_parity_collapse_carrier
  conclusion_z2torsor_square_parity_collapse_flip_flip :
    ∀ x,
      conclusion_z2torsor_square_parity_collapse_flip
          (conclusion_z2torsor_square_parity_collapse_flip x) =
        x

/-- The relative square difference: two entries have even difference exactly when they agree. -/
def conclusion_z2torsor_square_parity_collapse_difference
    (P : conclusion_z2torsor_square_parity_collapse_z2_torsor)
    (x y : P.conclusion_z2torsor_square_parity_collapse_carrier) : Bool :=
  letI := P.conclusion_z2torsor_square_parity_collapse_decidable_eq
  decide (x = y)

/-- Diagonal `Z₂`-orbit relation on `P × P`. -/
def conclusion_z2torsor_square_parity_collapse_diagonal_related
    (P : conclusion_z2torsor_square_parity_collapse_z2_torsor)
    (a b :
      P.conclusion_z2torsor_square_parity_collapse_carrier ×
        P.conclusion_z2torsor_square_parity_collapse_carrier) : Prop :=
  b = a ∨
    b =
      (P.conclusion_z2torsor_square_parity_collapse_flip a.1,
        P.conclusion_z2torsor_square_parity_collapse_flip a.2)

/-- The diagonal quotient of the square by simultaneous `Z₂`-translation. -/
def conclusion_z2torsor_square_parity_collapse_diagonal_setoid
    (P : conclusion_z2torsor_square_parity_collapse_z2_torsor) :
    Setoid
      (P.conclusion_z2torsor_square_parity_collapse_carrier ×
        P.conclusion_z2torsor_square_parity_collapse_carrier) where
  r := conclusion_z2torsor_square_parity_collapse_diagonal_related P
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro a
      exact Or.inl rfl
    · intro a b h
      rcases h with h | h
      · subst b
        exact Or.inl rfl
      · subst b
        refine Or.inr ?_
        ext <;> simp [P.conclusion_z2torsor_square_parity_collapse_flip_flip]
    · intro a b c hab hbc
      rcases hab with hab | hab
      · subst b
        exact hbc
      · subst b
        rcases hbc with hbc | hbc
        · subst c
          exact Or.inr rfl
        · subst c
          refine Or.inl ?_
          ext <;> simp [P.conclusion_z2torsor_square_parity_collapse_flip_flip]

/-- The relative difference descends to the diagonal quotient. -/
def conclusion_z2torsor_square_parity_collapse_quotient_difference
    (P : conclusion_z2torsor_square_parity_collapse_z2_torsor) :
    Quot (conclusion_z2torsor_square_parity_collapse_diagonal_setoid P) → Bool :=
  Quot.lift
    (fun a =>
      conclusion_z2torsor_square_parity_collapse_difference P a.1 a.2)
    (by
      intro a b h
      rcases h with h | h
      · subst b
        rfl
      · subst b
        unfold conclusion_z2torsor_square_parity_collapse_difference
        by_cases hxy : a.1 = a.2
        · simp [hxy]
        · have hflip :
            P.conclusion_z2torsor_square_parity_collapse_flip a.1 ≠
              P.conclusion_z2torsor_square_parity_collapse_flip a.2 := by
              intro h
              apply hxy
              have hc :=
                congrArg P.conclusion_z2torsor_square_parity_collapse_flip h
              simpa [P.conclusion_z2torsor_square_parity_collapse_flip_flip] using hc
          simp [hxy, hflip])

/-- Parity of a tensor power after cancelling square factors. -/
def conclusion_z2torsor_square_parity_collapse_tensor_parity : ℕ → Bool
  | 0 => false
  | 1 => true
  | n + 2 => conclusion_z2torsor_square_parity_collapse_tensor_parity n

/-- Concrete conclusion for the square quotient and tensor parity collapse. -/
def conclusion_z2torsor_square_parity_collapse_statement
    (P : conclusion_z2torsor_square_parity_collapse_z2_torsor) : Prop :=
  (∀ a :
      P.conclusion_z2torsor_square_parity_collapse_carrier ×
        P.conclusion_z2torsor_square_parity_collapse_carrier,
      conclusion_z2torsor_square_parity_collapse_quotient_difference P
          (Quot.mk (conclusion_z2torsor_square_parity_collapse_diagonal_setoid P) a) =
        conclusion_z2torsor_square_parity_collapse_difference P a.1 a.2) ∧
    (∀ a :
      P.conclusion_z2torsor_square_parity_collapse_carrier ×
        P.conclusion_z2torsor_square_parity_collapse_carrier,
      conclusion_z2torsor_square_parity_collapse_difference P
          (P.conclusion_z2torsor_square_parity_collapse_flip a.1)
          (P.conclusion_z2torsor_square_parity_collapse_flip a.2) =
        conclusion_z2torsor_square_parity_collapse_difference P a.1 a.2) ∧
      ∀ n,
        conclusion_z2torsor_square_parity_collapse_tensor_parity (n + 2) =
          conclusion_z2torsor_square_parity_collapse_tensor_parity n

/-- Paper label: `prop:conclusion-z2torsor-square-parity-collapse`. -/
theorem paper_conclusion_z2torsor_square_parity_collapse
    (P : conclusion_z2torsor_square_parity_collapse_z2_torsor) :
    conclusion_z2torsor_square_parity_collapse_statement P := by
  refine ⟨?_, ?_, ?_⟩
  · intro a
    rfl
  · intro a
    unfold conclusion_z2torsor_square_parity_collapse_difference
    by_cases hxy : a.1 = a.2
    · simp [hxy]
    · have hflip :
        P.conclusion_z2torsor_square_parity_collapse_flip a.1 ≠
          P.conclusion_z2torsor_square_parity_collapse_flip a.2 := by
          intro h
          apply hxy
          have hc := congrArg P.conclusion_z2torsor_square_parity_collapse_flip h
          simpa [P.conclusion_z2torsor_square_parity_collapse_flip_flip] using hc
      simp [hxy, hflip]
  · intro n
    induction n using Nat.twoStepInduction with
    | zero => rfl
    | one => rfl
    | more n _ _ => rfl

end Omega.Conclusion
