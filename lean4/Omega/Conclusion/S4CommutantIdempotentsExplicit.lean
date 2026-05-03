import Mathlib.Tactic

namespace Omega.Conclusion

/-- The trivial eigenvalue of the 40-block rank-three adjacency operator. -/
def conclusion_s4_40blocks_commutant_idempotents_explicit_lambda_triv : ℚ := 12

/-- The 24-dimensional eigenvalue. -/
def conclusion_s4_40blocks_commutant_idempotents_explicit_lambda_24 : ℚ := 2

/-- The 15-dimensional eigenvalue. -/
def conclusion_s4_40blocks_commutant_idempotents_explicit_lambda_15 : ℚ := -4

/-- Lagrange idempotent for the trivial eigenspace. -/
def conclusion_s4_40blocks_commutant_idempotents_explicit_e_triv (x : ℚ) : ℚ :=
  ((x - 2) * (x + 4)) / 160

/-- Lagrange idempotent for the eigenvalue `2` eigenspace. -/
def conclusion_s4_40blocks_commutant_idempotents_explicit_e_24 (x : ℚ) : ℚ :=
  -((x - 12) * (x + 4)) / 60

/-- Lagrange idempotent for the eigenvalue `-4` eigenspace. -/
def conclusion_s4_40blocks_commutant_idempotents_explicit_e_15 (x : ℚ) : ℚ :=
  ((x - 12) * (x - 2)) / 96

/-- The three eigenvalues carried by the rank-three decomposition. -/
def conclusion_s4_40blocks_commutant_idempotents_explicit_eigenvalue (i : Fin 3) : ℚ :=
  ![conclusion_s4_40blocks_commutant_idempotents_explicit_lambda_triv,
    conclusion_s4_40blocks_commutant_idempotents_explicit_lambda_24,
    conclusion_s4_40blocks_commutant_idempotents_explicit_lambda_15] i

/-- The three Lagrange idempotent polynomials. -/
def conclusion_s4_40blocks_commutant_idempotents_explicit_idempotent (i : Fin 3)
    (x : ℚ) : ℚ :=
  ![conclusion_s4_40blocks_commutant_idempotents_explicit_e_triv,
    conclusion_s4_40blocks_commutant_idempotents_explicit_e_24,
    conclusion_s4_40blocks_commutant_idempotents_explicit_e_15] i x

/-- Paper-facing explicit spectral-idempotent certificate for
`thm:conclusion-s4-40blocks-commutant-idempotents-explicit`. -/
def conclusion_s4_40blocks_commutant_idempotents_explicit_statement : Prop :=
  (∀ x : ℚ,
    conclusion_s4_40blocks_commutant_idempotents_explicit_e_triv x +
        conclusion_s4_40blocks_commutant_idempotents_explicit_e_24 x +
        conclusion_s4_40blocks_commutant_idempotents_explicit_e_15 x = 1) ∧
    (∀ i j : Fin 3,
      conclusion_s4_40blocks_commutant_idempotents_explicit_idempotent i
          (conclusion_s4_40blocks_commutant_idempotents_explicit_eigenvalue j) =
        if i = j then 1 else 0) ∧
    (∀ i j : Fin 3,
      conclusion_s4_40blocks_commutant_idempotents_explicit_idempotent i
          (conclusion_s4_40blocks_commutant_idempotents_explicit_eigenvalue j) *
        conclusion_s4_40blocks_commutant_idempotents_explicit_idempotent i
          (conclusion_s4_40blocks_commutant_idempotents_explicit_eigenvalue j) =
        conclusion_s4_40blocks_commutant_idempotents_explicit_idempotent i
          (conclusion_s4_40blocks_commutant_idempotents_explicit_eigenvalue j)) ∧
    (∀ i k j : Fin 3, i ≠ k →
      conclusion_s4_40blocks_commutant_idempotents_explicit_idempotent i
          (conclusion_s4_40blocks_commutant_idempotents_explicit_eigenvalue j) *
        conclusion_s4_40blocks_commutant_idempotents_explicit_idempotent k
          (conclusion_s4_40blocks_commutant_idempotents_explicit_eigenvalue j) = 0)

/-- Paper label: `thm:conclusion-s4-40blocks-commutant-idempotents-explicit`. -/
theorem paper_conclusion_s4_40blocks_commutant_idempotents_explicit :
    conclusion_s4_40blocks_commutant_idempotents_explicit_statement := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    unfold conclusion_s4_40blocks_commutant_idempotents_explicit_e_triv
      conclusion_s4_40blocks_commutant_idempotents_explicit_e_24
      conclusion_s4_40blocks_commutant_idempotents_explicit_e_15
    ring
  · intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [conclusion_s4_40blocks_commutant_idempotents_explicit_idempotent,
        conclusion_s4_40blocks_commutant_idempotents_explicit_eigenvalue,
        conclusion_s4_40blocks_commutant_idempotents_explicit_e_triv,
        conclusion_s4_40blocks_commutant_idempotents_explicit_e_24,
        conclusion_s4_40blocks_commutant_idempotents_explicit_e_15,
        conclusion_s4_40blocks_commutant_idempotents_explicit_lambda_triv,
        conclusion_s4_40blocks_commutant_idempotents_explicit_lambda_24,
        conclusion_s4_40blocks_commutant_idempotents_explicit_lambda_15]
  · intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [conclusion_s4_40blocks_commutant_idempotents_explicit_idempotent,
        conclusion_s4_40blocks_commutant_idempotents_explicit_eigenvalue,
        conclusion_s4_40blocks_commutant_idempotents_explicit_e_triv,
        conclusion_s4_40blocks_commutant_idempotents_explicit_e_24,
        conclusion_s4_40blocks_commutant_idempotents_explicit_e_15,
        conclusion_s4_40blocks_commutant_idempotents_explicit_lambda_triv,
        conclusion_s4_40blocks_commutant_idempotents_explicit_lambda_24,
        conclusion_s4_40blocks_commutant_idempotents_explicit_lambda_15]
  · intro i k j hik
    fin_cases i <;> fin_cases k <;> try contradiction
    all_goals
      fin_cases j <;>
      norm_num [conclusion_s4_40blocks_commutant_idempotents_explicit_idempotent,
        conclusion_s4_40blocks_commutant_idempotents_explicit_eigenvalue,
        conclusion_s4_40blocks_commutant_idempotents_explicit_e_triv,
        conclusion_s4_40blocks_commutant_idempotents_explicit_e_24,
        conclusion_s4_40blocks_commutant_idempotents_explicit_e_15,
        conclusion_s4_40blocks_commutant_idempotents_explicit_lambda_triv,
        conclusion_s4_40blocks_commutant_idempotents_explicit_lambda_24,
        conclusion_s4_40blocks_commutant_idempotents_explicit_lambda_15]

end Omega.Conclusion
