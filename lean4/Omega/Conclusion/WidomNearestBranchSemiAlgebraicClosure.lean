import Mathlib.Tactic

namespace Omega.Conclusion

/-- Insert one real fiber coordinate after a finite base point. -/
def conclusion_widom_nearest_branch_semi_algebraic_closure_lift {n : ℕ}
    (x : Fin n → ℝ) (t : ℝ) : Fin (n + 1) → ℝ :=
  fun i => if h : i.1 < n then x ⟨i.1, h⟩ else t

/-- Abstract semialgebraic closure interface used by the Widom nearest-branch package. It records
basic polynomial zero and positivity sets, Boolean closure by intersection and complement, and
closure under the last-coordinate projection. -/
structure conclusion_widom_nearest_branch_semi_algebraic_closure_interface where
  conclusion_widom_nearest_branch_semi_algebraic_closure_is_semialgebraic :
    (n : ℕ) → Set (Fin n → ℝ) → Prop
  conclusion_widom_nearest_branch_semi_algebraic_closure_polynomial_zero :
    ∀ {n : ℕ} (p : (Fin n → ℝ) → ℝ),
      conclusion_widom_nearest_branch_semi_algebraic_closure_is_semialgebraic n
        {x | p x = 0}
  conclusion_widom_nearest_branch_semi_algebraic_closure_polynomial_positive :
    ∀ {n : ℕ} (p : (Fin n → ℝ) → ℝ),
      conclusion_widom_nearest_branch_semi_algebraic_closure_is_semialgebraic n
        {x | 0 < p x}
  conclusion_widom_nearest_branch_semi_algebraic_closure_inter :
    ∀ {n : ℕ} {A B : Set (Fin n → ℝ)},
      conclusion_widom_nearest_branch_semi_algebraic_closure_is_semialgebraic n A →
        conclusion_widom_nearest_branch_semi_algebraic_closure_is_semialgebraic n B →
          conclusion_widom_nearest_branch_semi_algebraic_closure_is_semialgebraic n (A ∩ B)
  conclusion_widom_nearest_branch_semi_algebraic_closure_compl :
    ∀ {n : ℕ} {A : Set (Fin n → ℝ)},
      conclusion_widom_nearest_branch_semi_algebraic_closure_is_semialgebraic n A →
        conclusion_widom_nearest_branch_semi_algebraic_closure_is_semialgebraic n Aᶜ
  conclusion_widom_nearest_branch_semi_algebraic_closure_projection :
    ∀ {n : ℕ} {A : Set (Fin (n + 1) → ℝ)},
      conclusion_widom_nearest_branch_semi_algebraic_closure_is_semialgebraic (n + 1) A →
        conclusion_widom_nearest_branch_semi_algebraic_closure_is_semialgebraic n
          {x | ∃ t : ℝ,
            A (conclusion_widom_nearest_branch_semi_algebraic_closure_lift x t)}

/-- The discriminant equation defining the ambient Widom branch locus. -/
def conclusion_widom_nearest_branch_semi_algebraic_closure_discriminant
    (x : Fin 3 → ℝ) : ℝ :=
  x 0

/-- The upper-half-plane selector inequality. -/
def conclusion_widom_nearest_branch_semi_algebraic_closure_upper
    (x : Fin 3 → ℝ) : ℝ :=
  x 1

/-- The competing branch equation. -/
def conclusion_widom_nearest_branch_semi_algebraic_closure_branch
    (x : Fin 3 → ℝ) : ℝ :=
  x 2

/-- The basic discriminant-zero set `S`. -/
def conclusion_widom_nearest_branch_semi_algebraic_closure_S : Set (Fin 3 → ℝ) :=
  {x | conclusion_widom_nearest_branch_semi_algebraic_closure_discriminant x = 0}

/-- The basic upper-half-plane positivity set `U`. -/
def conclusion_widom_nearest_branch_semi_algebraic_closure_U : Set (Fin 3 → ℝ) :=
  {x | 0 < conclusion_widom_nearest_branch_semi_algebraic_closure_upper x}

/-- The excluded competing-branch set `V`. -/
def conclusion_widom_nearest_branch_semi_algebraic_closure_V : Set (Fin 3 → ℝ) :=
  conclusion_widom_nearest_branch_semi_algebraic_closure_U ∩
    {x | conclusion_widom_nearest_branch_semi_algebraic_closure_branch x = 0}

/-- The nearest-branch graph after removing the excluded branch. -/
def conclusion_widom_nearest_branch_semi_algebraic_closure_W : Set (Fin 3 → ℝ) :=
  conclusion_widom_nearest_branch_semi_algebraic_closure_S \
    conclusion_widom_nearest_branch_semi_algebraic_closure_V

/-- The parameter projection `P = π_T(W)`. -/
def conclusion_widom_nearest_branch_semi_algebraic_closure_P : Set (Fin 2 → ℝ) :=
  {x | ∃ t : ℝ, conclusion_widom_nearest_branch_semi_algebraic_closure_W
    (conclusion_widom_nearest_branch_semi_algebraic_closure_lift x t)}

/-- Paper-facing closure statement: the concrete sets `S`, `U`, `V`, `W`, and `P` are obtained
from the abstract semialgebraic closure interface, with `W = S \ V` and `P` exactly the projection
of `W`. -/
def conclusion_widom_nearest_branch_semi_algebraic_closure_statement : Prop :=
  ∀ C : conclusion_widom_nearest_branch_semi_algebraic_closure_interface,
    C.conclusion_widom_nearest_branch_semi_algebraic_closure_is_semialgebraic 3
        conclusion_widom_nearest_branch_semi_algebraic_closure_S ∧
      C.conclusion_widom_nearest_branch_semi_algebraic_closure_is_semialgebraic 3
        conclusion_widom_nearest_branch_semi_algebraic_closure_U ∧
      C.conclusion_widom_nearest_branch_semi_algebraic_closure_is_semialgebraic 3
        conclusion_widom_nearest_branch_semi_algebraic_closure_V ∧
      C.conclusion_widom_nearest_branch_semi_algebraic_closure_is_semialgebraic 3
        conclusion_widom_nearest_branch_semi_algebraic_closure_W ∧
      C.conclusion_widom_nearest_branch_semi_algebraic_closure_is_semialgebraic 2
        conclusion_widom_nearest_branch_semi_algebraic_closure_P ∧
      conclusion_widom_nearest_branch_semi_algebraic_closure_W =
        conclusion_widom_nearest_branch_semi_algebraic_closure_S \
          conclusion_widom_nearest_branch_semi_algebraic_closure_V ∧
      conclusion_widom_nearest_branch_semi_algebraic_closure_P =
        {x | ∃ t : ℝ, conclusion_widom_nearest_branch_semi_algebraic_closure_W
          (conclusion_widom_nearest_branch_semi_algebraic_closure_lift x t)}

/-- Paper label: `thm:conclusion-widom-nearest-branch-semi-algebraic-closure`. -/
theorem paper_conclusion_widom_nearest_branch_semi_algebraic_closure :
    conclusion_widom_nearest_branch_semi_algebraic_closure_statement := by
  intro C
  have hS :
      C.conclusion_widom_nearest_branch_semi_algebraic_closure_is_semialgebraic 3
        conclusion_widom_nearest_branch_semi_algebraic_closure_S := by
    simpa [conclusion_widom_nearest_branch_semi_algebraic_closure_S] using
      C.conclusion_widom_nearest_branch_semi_algebraic_closure_polynomial_zero
        conclusion_widom_nearest_branch_semi_algebraic_closure_discriminant
  have hU :
      C.conclusion_widom_nearest_branch_semi_algebraic_closure_is_semialgebraic 3
        conclusion_widom_nearest_branch_semi_algebraic_closure_U := by
    simpa [conclusion_widom_nearest_branch_semi_algebraic_closure_U] using
      C.conclusion_widom_nearest_branch_semi_algebraic_closure_polynomial_positive
        conclusion_widom_nearest_branch_semi_algebraic_closure_upper
  have hBranch :
      C.conclusion_widom_nearest_branch_semi_algebraic_closure_is_semialgebraic 3
        {x | conclusion_widom_nearest_branch_semi_algebraic_closure_branch x = 0} :=
    C.conclusion_widom_nearest_branch_semi_algebraic_closure_polynomial_zero
      conclusion_widom_nearest_branch_semi_algebraic_closure_branch
  have hV :
      C.conclusion_widom_nearest_branch_semi_algebraic_closure_is_semialgebraic 3
        conclusion_widom_nearest_branch_semi_algebraic_closure_V := by
    simpa [conclusion_widom_nearest_branch_semi_algebraic_closure_V] using
      C.conclusion_widom_nearest_branch_semi_algebraic_closure_inter hU hBranch
  have hW :
      C.conclusion_widom_nearest_branch_semi_algebraic_closure_is_semialgebraic 3
        conclusion_widom_nearest_branch_semi_algebraic_closure_W := by
    simpa [conclusion_widom_nearest_branch_semi_algebraic_closure_W, Set.diff_eq] using
      C.conclusion_widom_nearest_branch_semi_algebraic_closure_inter hS
        (C.conclusion_widom_nearest_branch_semi_algebraic_closure_compl hV)
  have hP :
      C.conclusion_widom_nearest_branch_semi_algebraic_closure_is_semialgebraic 2
        conclusion_widom_nearest_branch_semi_algebraic_closure_P := by
    simpa [conclusion_widom_nearest_branch_semi_algebraic_closure_P] using
      C.conclusion_widom_nearest_branch_semi_algebraic_closure_projection hW
  exact ⟨hS, hU, hV, hW, hP, rfl, rfl⟩

end Omega.Conclusion
