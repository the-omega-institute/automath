import Mathlib.Data.List.Basic
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Tactic

namespace Omega.DerivedConsequences

/-- Concrete factor witness for the genus-`49` Hurwitz decomposition ledger. -/
structure derived_hurwitz_genus49_square_cube_locking_factor where
  dimension : ℕ
  multiplicity : ℕ
deriving DecidableEq, Repr

/-- The `J(H)` factor occurs once. -/
def derived_hurwitz_genus49_square_cube_locking_j_h :
    derived_hurwitz_genus49_square_cube_locking_factor :=
  ⟨1, 1⟩

/-- The `J(Z)` factor is the unique square block, appearing with multiplicity `2`. -/
def derived_hurwitz_genus49_square_cube_locking_j_z :
    derived_hurwitz_genus49_square_cube_locking_factor :=
  ⟨6, 2⟩

/-- The `J(C_F)` factor is one of the cube blocks. -/
def derived_hurwitz_genus49_square_cube_locking_j_c_f :
    derived_hurwitz_genus49_square_cube_locking_factor :=
  ⟨8, 3⟩

/-- The Prym factor `P` is the second cube block. -/
def derived_hurwitz_genus49_square_cube_locking_p :
    derived_hurwitz_genus49_square_cube_locking_factor :=
  ⟨4, 3⟩

/-- Ordered factor ledger `(J(H), J(Z), J(C_F), P)`. -/
def derived_hurwitz_genus49_square_cube_locking_factors :
    List derived_hurwitz_genus49_square_cube_locking_factor :=
  [derived_hurwitz_genus49_square_cube_locking_j_h,
    derived_hurwitz_genus49_square_cube_locking_j_z,
    derived_hurwitz_genus49_square_cube_locking_j_c_f,
    derived_hurwitz_genus49_square_cube_locking_p]

/-- Weighted contribution of a factor to the ambient genus count. -/
def derived_hurwitz_genus49_square_cube_locking_weighted_dimension
    (F : derived_hurwitz_genus49_square_cube_locking_factor) : ℕ :=
  F.dimension * F.multiplicity

/-- Total genus contribution of the four-factor ledger. -/
def derived_hurwitz_genus49_square_cube_locking_total_dimension : ℕ :=
  (derived_hurwitz_genus49_square_cube_locking_factors.map
      derived_hurwitz_genus49_square_cube_locking_weighted_dimension).sum

/-- Dimension ledger for the bridge identification `Prym(C_6/H) ~ J(Z)^2`. -/
def derived_hurwitz_genus49_square_cube_locking_prym_dimension : ℕ :=
  2 * derived_hurwitz_genus49_square_cube_locking_j_z.dimension

/-- Paper label: `thm:derived-hurwitz-genus49-square-cube-locking`. The concrete ledger
`J(H), J(Z), J(C_F), P` has multiplicities `1, 2, 3, 3`; the bridge `Prym(C_6/H) ~ J(Z)^2`
appears as the doubled `J(Z)` dimension; and the genus count `1*1 + 2*6 + 3*8 + 3*4 = 49`
shows that the square block is the unique even-multiplicity sector. -/
theorem paper_derived_hurwitz_genus49_square_cube_locking :
    derived_hurwitz_genus49_square_cube_locking_factors.map
        derived_hurwitz_genus49_square_cube_locking_factor.dimension =
      [1, 6, 8, 4] ∧
    derived_hurwitz_genus49_square_cube_locking_factors.map
        derived_hurwitz_genus49_square_cube_locking_factor.multiplicity =
      [1, 2, 3, 3] ∧
    derived_hurwitz_genus49_square_cube_locking_prym_dimension =
      2 * derived_hurwitz_genus49_square_cube_locking_j_z.dimension ∧
    derived_hurwitz_genus49_square_cube_locking_total_dimension = 49 ∧
    Even derived_hurwitz_genus49_square_cube_locking_j_z.multiplicity ∧
    ¬ Even derived_hurwitz_genus49_square_cube_locking_j_h.multiplicity ∧
    ¬ Even derived_hurwitz_genus49_square_cube_locking_j_c_f.multiplicity ∧
    ¬ Even derived_hurwitz_genus49_square_cube_locking_p.multiplicity := by
  native_decide

end Omega.DerivedConsequences
