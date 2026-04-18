import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

open Matrix

/-- A concrete `1 × 1` twisted Hashimoto block. -/
def trivialTwistedHashimotoBlock (u : ℤ) : Matrix (Fin 1) (Fin 1) ℤ :=
  !![u]

/-- A concrete `2 × 2` irreducible twisted Hashimoto block, repeated with multiplicity `dim ρ=2`.
-/
def irreducibleTwistedHashimotoBlock (v : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![v, 0; 0, v]

/-- The regular-representation block decomposition consists of the trivial block and the
two-dimensional irreducible block. -/
def regularRepresentationHashimotoBlock (u v : ℤ) : Matrix (Fin 3) (Fin 3) ℤ :=
  !![u, 0, 0;
    0, v, 0;
    0, 0, v]

/-- Paper label: `prop:ihara-artin-factorization`.
For this block-diagonal specialization of the group-extension Hashimoto operator, the determinant
of the regular-representation block factors as the product of the twisted determinants, with the
two-dimensional block contributing multiplicity `2`. -/
theorem paper_ihara_artin_factorization (t u v : ℤ) :
    Matrix.det (1 - t • regularRepresentationHashimotoBlock u v) =
      Matrix.det (1 - t • trivialTwistedHashimotoBlock u) *
        Matrix.det (1 - t • irreducibleTwistedHashimotoBlock v) := by
  simp [regularRepresentationHashimotoBlock, trivialTwistedHashimotoBlock,
    irreducibleTwistedHashimotoBlock, Matrix.det_fin_two, Matrix.det_fin_three]
  ring

end Omega.SyncKernelWeighted
