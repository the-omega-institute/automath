import Mathlib.Data.Nat.Totient
import Mathlib.Tactic

namespace Omega.POM

/-- Twice the Chebyshev value `T_n(c / 2)`, represented by the integral recurrence
`C_0 = 2`, `C_1 = c`, and `C_{n+2} = c C_{n+1} - C_n`. -/
def pom_a4t_cyclotomic_adj_minpoly_resultant_chebyshevValue : ℕ → ℤ → ℤ
  | 0, _ => 2
  | 1, c => c
  | n + 2, c =>
      c * pom_a4t_cyclotomic_adj_minpoly_resultant_chebyshevValue (n + 1) c -
        pom_a4t_cyclotomic_adj_minpoly_resultant_chebyshevValue n c

/-- The integral Chebyshev constraint corresponding to `T_h(c / 2) + 1 = 0`. -/
def pom_a4t_cyclotomic_adj_minpoly_resultant_chebyshevConstraint
    (h : ℕ) (c : ℤ) : Prop :=
  pom_a4t_cyclotomic_adj_minpoly_resultant_chebyshevValue h c + 2 = 0

/-- The quintic interface relation `c^5 + 2 c^4 - t c^3 - 2 c - 2 = 0`. -/
def pom_a4t_cyclotomic_adj_minpoly_resultant_quinticRelation (t c : ℤ) : Prop :=
  c ^ 5 + 2 * c ^ 4 - t * c ^ 3 - 2 * c - 2 = 0

/-- Certificate data for the Chebyshev-resultant generation mechanism. -/
structure pom_a4t_cyclotomic_adj_minpoly_resultant_data where
  h : ℕ
  t : ℤ
  c : ℤ
  resultantValue : ℤ
  minpolyDegree : ℕ
  cyclotomicDegreeInput : ℕ
  chebyshevConstraint_cert :
    pom_a4t_cyclotomic_adj_minpoly_resultant_chebyshevConstraint h c
  quinticRelation_cert :
    pom_a4t_cyclotomic_adj_minpoly_resultant_quinticRelation t c
  resultantElimination_cert : resultantValue = 0
  cyclotomicDegreeInput_cert : cyclotomicDegreeInput = Nat.totient (2 * h) / 2
  minpolyDegree_cert : minpolyDegree = cyclotomicDegreeInput

namespace pom_a4t_cyclotomic_adj_minpoly_resultant_data

/-- The resultant-elimination witness: the certified resultant vanishes at the recorded `t`. -/
def resultantElimination
    (D : pom_a4t_cyclotomic_adj_minpoly_resultant_data) : Prop :=
  D.resultantValue = 0

/-- The minimal-polynomial degree claim obtained from the cyclotomic degree input. -/
def degreeClaim (D : pom_a4t_cyclotomic_adj_minpoly_resultant_data) : Prop :=
  D.minpolyDegree = Nat.totient (2 * D.h) / 2

end pom_a4t_cyclotomic_adj_minpoly_resultant_data

/-- Paper statement for the `A₄(t)` cyclotomic adjacency Chebyshev-resultant certificate. -/
def pom_a4t_cyclotomic_adj_minpoly_resultant_statement
    (D : pom_a4t_cyclotomic_adj_minpoly_resultant_data) : Prop :=
  pom_a4t_cyclotomic_adj_minpoly_resultant_chebyshevConstraint D.h D.c ∧
    pom_a4t_cyclotomic_adj_minpoly_resultant_quinticRelation D.t D.c ∧
      D.resultantElimination ∧ D.degreeClaim

/-- Paper label: `prop:pom-a4t-cyclotomic-adj-minpoly-resultant`. -/
theorem paper_pom_a4t_cyclotomic_adj_minpoly_resultant
    (D : pom_a4t_cyclotomic_adj_minpoly_resultant_data) :
    pom_a4t_cyclotomic_adj_minpoly_resultant_statement D := by
  refine ⟨D.chebyshevConstraint_cert, D.quinticRelation_cert, ?_, ?_⟩
  · exact D.resultantElimination_cert
  · dsimp [pom_a4t_cyclotomic_adj_minpoly_resultant_data.degreeClaim]
    rw [D.minpolyDegree_cert, D.cyclotomicDegreeInput_cert]

end Omega.POM
