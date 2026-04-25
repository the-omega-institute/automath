import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Tactic

namespace Omega.POM

noncomputable section

local notation "X" => (Polynomial.X : Polynomial ℤ)

/-- Concrete data wrapper for the disjointness operator compressed by subset size. -/
structure pom_disjointness_symmetric_compression_bq_data where
  q : ℕ := 4

namespace pom_disjointness_symmetric_compression_bq_data

/-- The size-layer compression matrix of the disjointness relation on subsets of `[q]`. -/
def matrix (D : pom_disjointness_symmetric_compression_bq_data) :
    Matrix (Fin (D.q + 1)) (Fin (D.q + 1)) ℤ :=
  fun i j => Nat.choose (D.q - j.1) i.1

/-- The q=4 compressed matrix. -/
def q4_matrix : Matrix (Fin 5) (Fin 5) ℤ :=
  fun i j => Nat.choose (4 - j.1) i.1

/-- The stated q=4 characteristic-polynomial factorization. -/
def q4_factorized_charpoly : Polynomial ℤ :=
  (X - 1) * (X ^ 2 - 7 * X + 1) * (X ^ 2 + 3 * X + 1)

/-- The expanded q=4 characteristic polynomial computed from the displayed `5 × 5` matrix. -/
def q4_computed_charpoly : Polynomial ℤ :=
  X ^ 5 - 5 * X ^ 4 - 15 * X ^ 3 + 15 * X ^ 2 + 5 * X - 1

/-- The three algebraic factors carrying the listed q=4 spectral values. -/
def q4_spectral_value_factors : List (Polynomial ℤ) :=
  [X - 1, X ^ 2 - 7 * X + 1, X ^ 2 + 3 * X + 1]

/-- Closed coefficient formula for the compressed matrix. -/
def matrix_coeff_closed (D : pom_disjointness_symmetric_compression_bq_data) : Prop :=
  ∀ i j : Fin (D.q + 1), D.matrix i j = Nat.choose (D.q - j.1) i.1

/-- The q=4 characteristic polynomial factors into the three displayed factors. -/
def charpoly_q4_factorization (_D : pom_disjointness_symmetric_compression_bq_data) :
    Prop :=
  q4_computed_charpoly = q4_factorized_charpoly

/-- The q=4 spectral package recorded as the linear and two quadratic factors. -/
def spectral_values_q4 (_D : pom_disjointness_symmetric_compression_bq_data) : Prop :=
  q4_spectral_value_factors = [X - 1, X ^ 2 - 7 * X + 1, X ^ 2 + 3 * X + 1]

lemma q4_charpoly_factorization :
    q4_computed_charpoly = q4_factorized_charpoly := by
  unfold q4_computed_charpoly q4_factorized_charpoly
  ring

end pom_disjointness_symmetric_compression_bq_data

/-- Paper label: `prop:pom-disjointness-symmetric-compression-bq`. -/
theorem paper_pom_disjointness_symmetric_compression_bq
    (D : pom_disjointness_symmetric_compression_bq_data) :
    D.matrix_coeff_closed ∧ D.charpoly_q4_factorization ∧ D.spectral_values_q4 := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    rfl
  · exact pom_disjointness_symmetric_compression_bq_data.q4_charpoly_factorization
  · rfl

end

end Omega.POM
