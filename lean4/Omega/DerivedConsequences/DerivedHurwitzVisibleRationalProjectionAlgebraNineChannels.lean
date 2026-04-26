import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

namespace Omega.DerivedConsequences

abbrev derived_hurwitz_visible_rational_projection_algebra_nine_channels_m2 :=
  Matrix (Fin 2) (Fin 2) ℚ

abbrev derived_hurwitz_visible_rational_projection_algebra_nine_channels_m3 :=
  Matrix (Fin 3) (Fin 3) ℚ

/-- Visible rational projection algebra with the scalar sector and the `2 × 2`, `3 × 3`, `3 × 3`
matrix blocks singled out as separate factors. -/
abbrev derived_hurwitz_visible_rational_projection_algebra_nine_channels_visible_algebra :=
  ℚ ×
    derived_hurwitz_visible_rational_projection_algebra_nine_channels_m2 ×
    derived_hurwitz_visible_rational_projection_algebra_nine_channels_m3 ×
    derived_hurwitz_visible_rational_projection_algebra_nine_channels_m3

/-- Diagonal primitive idempotent in a matrix block. -/
def derived_hurwitz_visible_rational_projection_algebra_nine_channels_diag_matrix
    {n : Type} [Fintype n] [DecidableEq n] (i : n) : Matrix n n ℚ :=
  Matrix.diagonal fun j => if j = i then 1 else 0

/-- Distinguished scalar channel. -/
def derived_hurwitz_visible_rational_projection_algebra_nine_channels_scalar_channel :
    derived_hurwitz_visible_rational_projection_algebra_nine_channels_visible_algebra :=
  (1, 0, 0, 0)

/-- Two primitive channels coming from the `M₂(ℚ)` factor. -/
def derived_hurwitz_visible_rational_projection_algebra_nine_channels_m2_channel (i : Fin 2) :
    derived_hurwitz_visible_rational_projection_algebra_nine_channels_visible_algebra :=
  (0, derived_hurwitz_visible_rational_projection_algebra_nine_channels_diag_matrix i, 0, 0)

/-- Three primitive channels coming from the first `M₃(ℚ)` factor. -/
def derived_hurwitz_visible_rational_projection_algebra_nine_channels_m3_left_channel (i : Fin 3) :
    derived_hurwitz_visible_rational_projection_algebra_nine_channels_visible_algebra :=
  (0, 0, derived_hurwitz_visible_rational_projection_algebra_nine_channels_diag_matrix i, 0)

/-- Three primitive channels coming from the second `M₃(ℚ)` factor. -/
def derived_hurwitz_visible_rational_projection_algebra_nine_channels_m3_right_channel (i : Fin 3) :
    derived_hurwitz_visible_rational_projection_algebra_nine_channels_visible_algebra :=
  (0, 0, 0, derived_hurwitz_visible_rational_projection_algebra_nine_channels_diag_matrix i)

private lemma derived_hurwitz_visible_rational_projection_algebra_nine_channels_diag_matrix_idempotent_fin2
    (i : Fin 2) :
    derived_hurwitz_visible_rational_projection_algebra_nine_channels_diag_matrix i *
        derived_hurwitz_visible_rational_projection_algebra_nine_channels_diag_matrix i =
      derived_hurwitz_visible_rational_projection_algebra_nine_channels_diag_matrix i := by
  ext a b
  fin_cases a <;> fin_cases b <;> fin_cases i <;>
    simp [derived_hurwitz_visible_rational_projection_algebra_nine_channels_diag_matrix,
      Matrix.mul_apply, Fin.sum_univ_two]

private lemma derived_hurwitz_visible_rational_projection_algebra_nine_channels_diag_matrix_idempotent_fin3
    (i : Fin 3) :
    derived_hurwitz_visible_rational_projection_algebra_nine_channels_diag_matrix i *
        derived_hurwitz_visible_rational_projection_algebra_nine_channels_diag_matrix i =
      derived_hurwitz_visible_rational_projection_algebra_nine_channels_diag_matrix i := by
  ext a b
  fin_cases a <;> fin_cases b <;> fin_cases i <;>
    simp [derived_hurwitz_visible_rational_projection_algebra_nine_channels_diag_matrix,
      Matrix.mul_apply, Fin.sum_univ_three]

private lemma derived_hurwitz_visible_rational_projection_algebra_nine_channels_diag_matrix_orthogonal_fin2
    {i j : Fin 2} (hij : i ≠ j) :
    derived_hurwitz_visible_rational_projection_algebra_nine_channels_diag_matrix i *
        derived_hurwitz_visible_rational_projection_algebra_nine_channels_diag_matrix j =
      0 := by
  ext a b
  fin_cases a <;> fin_cases b <;> fin_cases i <;> fin_cases j <;>
    simp [derived_hurwitz_visible_rational_projection_algebra_nine_channels_diag_matrix,
      Matrix.mul_apply, Fin.sum_univ_two] at hij ⊢

private lemma derived_hurwitz_visible_rational_projection_algebra_nine_channels_diag_matrix_orthogonal_fin3
    {i j : Fin 3} (hij : i ≠ j) :
    derived_hurwitz_visible_rational_projection_algebra_nine_channels_diag_matrix i *
        derived_hurwitz_visible_rational_projection_algebra_nine_channels_diag_matrix j =
      0 := by
  ext a b
  fin_cases a <;> fin_cases b <;> fin_cases i <;> fin_cases j <;>
    simp [derived_hurwitz_visible_rational_projection_algebra_nine_channels_diag_matrix,
      Matrix.mul_apply, Fin.sum_univ_three] at hij ⊢

private lemma derived_hurwitz_visible_rational_projection_algebra_nine_channels_diag_matrix_nonzero_fin2
    (i : Fin 2) :
    derived_hurwitz_visible_rational_projection_algebra_nine_channels_diag_matrix i ≠ 0 := by
  intro h
  have hentry := congrArg (fun M => M i i) h
  simp [derived_hurwitz_visible_rational_projection_algebra_nine_channels_diag_matrix] at hentry

private lemma derived_hurwitz_visible_rational_projection_algebra_nine_channels_diag_matrix_nonzero_fin3
    (i : Fin 3) :
    derived_hurwitz_visible_rational_projection_algebra_nine_channels_diag_matrix i ≠ 0 := by
  intro h
  have hentry := congrArg (fun M => M i i) h
  simp [derived_hurwitz_visible_rational_projection_algebra_nine_channels_diag_matrix] at hentry

/-- Concrete visible-channel package: one scalar channel, two `M₂` channels, three channels in
each `M₃` block, all witnessed by diagonal primitive idempotents with pairwise-orthogonal support,
so the visible channel count is `1 + 2 + 3 + 3 = 9`. -/
def derived_hurwitz_visible_rational_projection_algebra_nine_channels_statement : Prop :=
  (derived_hurwitz_visible_rational_projection_algebra_nine_channels_scalar_channel *
      derived_hurwitz_visible_rational_projection_algebra_nine_channels_scalar_channel =
    derived_hurwitz_visible_rational_projection_algebra_nine_channels_scalar_channel) ∧
    derived_hurwitz_visible_rational_projection_algebra_nine_channels_scalar_channel ≠ 0 ∧
    (∀ i : Fin 2,
      derived_hurwitz_visible_rational_projection_algebra_nine_channels_m2_channel i *
          derived_hurwitz_visible_rational_projection_algebra_nine_channels_m2_channel i =
        derived_hurwitz_visible_rational_projection_algebra_nine_channels_m2_channel i ∧
        derived_hurwitz_visible_rational_projection_algebra_nine_channels_m2_channel i ≠ 0) ∧
    (∀ i : Fin 3,
      derived_hurwitz_visible_rational_projection_algebra_nine_channels_m3_left_channel i *
          derived_hurwitz_visible_rational_projection_algebra_nine_channels_m3_left_channel i =
        derived_hurwitz_visible_rational_projection_algebra_nine_channels_m3_left_channel i ∧
        derived_hurwitz_visible_rational_projection_algebra_nine_channels_m3_left_channel i ≠ 0) ∧
    (∀ i : Fin 3,
      derived_hurwitz_visible_rational_projection_algebra_nine_channels_m3_right_channel i *
          derived_hurwitz_visible_rational_projection_algebra_nine_channels_m3_right_channel i =
        derived_hurwitz_visible_rational_projection_algebra_nine_channels_m3_right_channel i ∧
        derived_hurwitz_visible_rational_projection_algebra_nine_channels_m3_right_channel i ≠ 0) ∧
    (∀ i j : Fin 2, i ≠ j →
      derived_hurwitz_visible_rational_projection_algebra_nine_channels_m2_channel i *
          derived_hurwitz_visible_rational_projection_algebra_nine_channels_m2_channel j =
        0) ∧
    (∀ i j : Fin 3, i ≠ j →
      derived_hurwitz_visible_rational_projection_algebra_nine_channels_m3_left_channel i *
          derived_hurwitz_visible_rational_projection_algebra_nine_channels_m3_left_channel j =
        0) ∧
    (∀ i j : Fin 3, i ≠ j →
      derived_hurwitz_visible_rational_projection_algebra_nine_channels_m3_right_channel i *
          derived_hurwitz_visible_rational_projection_algebra_nine_channels_m3_right_channel j =
        0) ∧
    (∀ i : Fin 2,
      derived_hurwitz_visible_rational_projection_algebra_nine_channels_scalar_channel *
          derived_hurwitz_visible_rational_projection_algebra_nine_channels_m2_channel i =
        0) ∧
    (∀ i : Fin 3,
      derived_hurwitz_visible_rational_projection_algebra_nine_channels_scalar_channel *
          derived_hurwitz_visible_rational_projection_algebra_nine_channels_m3_left_channel i =
        0) ∧
    (∀ i : Fin 3,
      derived_hurwitz_visible_rational_projection_algebra_nine_channels_scalar_channel *
          derived_hurwitz_visible_rational_projection_algebra_nine_channels_m3_right_channel i =
        0) ∧
    (∀ i : Fin 2, ∀ j : Fin 3,
      derived_hurwitz_visible_rational_projection_algebra_nine_channels_m2_channel i *
          derived_hurwitz_visible_rational_projection_algebra_nine_channels_m3_left_channel j =
        0) ∧
    (∀ i : Fin 2, ∀ j : Fin 3,
      derived_hurwitz_visible_rational_projection_algebra_nine_channels_m2_channel i *
          derived_hurwitz_visible_rational_projection_algebra_nine_channels_m3_right_channel j =
        0) ∧
    (∀ i j : Fin 3,
      derived_hurwitz_visible_rational_projection_algebra_nine_channels_m3_left_channel i *
          derived_hurwitz_visible_rational_projection_algebra_nine_channels_m3_right_channel j =
        0) ∧
    Fintype.card (Fin 1) = 1 ∧
    Fintype.card (Fin 2) = 2 ∧
    Fintype.card (Fin 3) = 3 ∧
    Fintype.card (Fin 1) + Fintype.card (Fin 2) + Fintype.card (Fin 3) + Fintype.card (Fin 3) = 9

/-- Paper label: `thm:derived-hurwitz-visible-rational-projection-algebra-nine-channels`. The
visible rational projection algebra decomposes into four center sectors
`ℚ × M₂(ℚ) × M₃(ℚ) × M₃(ℚ)`, and the diagonal matrix units yield one, two, three, and three
pairwise orthogonal nonzero idempotent channels respectively, for a total of nine visible
channels. -/
theorem paper_derived_hurwitz_visible_rational_projection_algebra_nine_channels :
    derived_hurwitz_visible_rational_projection_algebra_nine_channels_statement := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [derived_hurwitz_visible_rational_projection_algebra_nine_channels_scalar_channel]
  · simp [derived_hurwitz_visible_rational_projection_algebra_nine_channels_scalar_channel]
  · intro i
    refine ⟨?_, ?_⟩
    · ext <;> simp [derived_hurwitz_visible_rational_projection_algebra_nine_channels_m2_channel,
        derived_hurwitz_visible_rational_projection_algebra_nine_channels_diag_matrix_idempotent_fin2]
    · intro h
      have h2 := congrArg Prod.snd h
      have h3 := congrArg Prod.fst h2
      exact
        derived_hurwitz_visible_rational_projection_algebra_nine_channels_diag_matrix_nonzero_fin2 i h3
  · intro i
    refine ⟨?_, ?_⟩
    · ext <;> simp [derived_hurwitz_visible_rational_projection_algebra_nine_channels_m3_left_channel,
        derived_hurwitz_visible_rational_projection_algebra_nine_channels_diag_matrix_idempotent_fin3]
    · intro h
      have h4 :
          derived_hurwitz_visible_rational_projection_algebra_nine_channels_diag_matrix i = 0 := by
        simpa [derived_hurwitz_visible_rational_projection_algebra_nine_channels_m3_left_channel]
          using congrArg (fun x => x.2.2.1) h
      exact
        derived_hurwitz_visible_rational_projection_algebra_nine_channels_diag_matrix_nonzero_fin3 i h4
  · intro i
    refine ⟨?_, ?_⟩
    · ext <;> simp [derived_hurwitz_visible_rational_projection_algebra_nine_channels_m3_right_channel,
        derived_hurwitz_visible_rational_projection_algebra_nine_channels_diag_matrix_idempotent_fin3]
    · intro h
      have h3 :
          derived_hurwitz_visible_rational_projection_algebra_nine_channels_diag_matrix i = 0 := by
        simpa [derived_hurwitz_visible_rational_projection_algebra_nine_channels_m3_right_channel]
          using congrArg (fun x => x.2.2.2) h
      exact
        derived_hurwitz_visible_rational_projection_algebra_nine_channels_diag_matrix_nonzero_fin3 i h3
  · intro i j hij
    ext <;> simp [derived_hurwitz_visible_rational_projection_algebra_nine_channels_m2_channel,
      derived_hurwitz_visible_rational_projection_algebra_nine_channels_diag_matrix_orthogonal_fin2
        hij]
  · intro i j hij
    ext <;> simp [derived_hurwitz_visible_rational_projection_algebra_nine_channels_m3_left_channel,
      derived_hurwitz_visible_rational_projection_algebra_nine_channels_diag_matrix_orthogonal_fin3
        hij]
  · intro i j hij
    ext <;> simp [derived_hurwitz_visible_rational_projection_algebra_nine_channels_m3_right_channel,
      derived_hurwitz_visible_rational_projection_algebra_nine_channels_diag_matrix_orthogonal_fin3
        hij]
  · intro i
    simp [derived_hurwitz_visible_rational_projection_algebra_nine_channels_scalar_channel,
      derived_hurwitz_visible_rational_projection_algebra_nine_channels_m2_channel]
  · intro i
    simp [derived_hurwitz_visible_rational_projection_algebra_nine_channels_scalar_channel,
      derived_hurwitz_visible_rational_projection_algebra_nine_channels_m3_left_channel]
  · intro i
    simp [derived_hurwitz_visible_rational_projection_algebra_nine_channels_scalar_channel,
      derived_hurwitz_visible_rational_projection_algebra_nine_channels_m3_right_channel]
  · intro i j
    simp [derived_hurwitz_visible_rational_projection_algebra_nine_channels_m2_channel,
      derived_hurwitz_visible_rational_projection_algebra_nine_channels_m3_left_channel]
  · intro i j
    simp [derived_hurwitz_visible_rational_projection_algebra_nine_channels_m2_channel,
      derived_hurwitz_visible_rational_projection_algebra_nine_channels_m3_right_channel]
  · intro i j
    simp [derived_hurwitz_visible_rational_projection_algebra_nine_channels_m3_left_channel,
      derived_hurwitz_visible_rational_projection_algebra_nine_channels_m3_right_channel]
  · simp
  · simp
  · simp

end Omega.DerivedConsequences
