import Mathlib.Tactic
import Omega.Folding.BinFold

open scoped BigOperators

namespace Omega.Zeta

/-- A concrete finite direct sum of matrix blocks over the Fibonacci block index set. The natural
number records the matrix size of each block. -/
structure xi_time_part60aca_morita_type_forgets_block_sizes_block_family (m : ℕ) where
  blockSize : Omega.X m → ℕ

/-- Morita reduction keeps one scalar summand for every block index. -/
noncomputable def xi_time_part60aca_morita_type_forgets_block_sizes_scalar_index_set {m : ℕ}
    (_F : xi_time_part60aca_morita_type_forgets_block_sizes_block_family m) :
    Finset (Omega.X m) :=
  Finset.univ

/-- The reduced positive cone is the finitely supported vector of scalar multiplicities. -/
abbrev xi_time_part60aca_morita_type_forgets_block_sizes_positive_cone (m : ℕ) :=
  Omega.X m → ℕ

/-- The block-size-free scalar count after Morita reduction. -/
noncomputable def xi_time_part60aca_morita_type_forgets_block_sizes_scalar_count {m : ℕ}
    (F : xi_time_part60aca_morita_type_forgets_block_sizes_block_family m) : ℕ :=
  (xi_time_part60aca_morita_type_forgets_block_sizes_scalar_index_set F).card

/-- Concrete statement: any two finite block families over the same Fibonacci index set have the
same Morita-reduced scalar index set and the scalar count is the Fibonacci block count. -/
def xi_time_part60aca_morita_type_forgets_block_sizes_statement (m : ℕ) : Prop :=
  ∀ F G : xi_time_part60aca_morita_type_forgets_block_sizes_block_family m,
    xi_time_part60aca_morita_type_forgets_block_sizes_scalar_index_set F =
      xi_time_part60aca_morita_type_forgets_block_sizes_scalar_index_set G ∧
    xi_time_part60aca_morita_type_forgets_block_sizes_scalar_count F = Nat.fib (m + 2) ∧
    xi_time_part60aca_morita_type_forgets_block_sizes_scalar_count G = Nat.fib (m + 2)

/-- Paper label: `thm:xi-time-part60aca-morita-type-forgets-block-sizes`. -/
theorem paper_xi_time_part60aca_morita_type_forgets_block_sizes (m : ℕ) :
    xi_time_part60aca_morita_type_forgets_block_sizes_statement m := by
  intro F G
  simp [xi_time_part60aca_morita_type_forgets_block_sizes_scalar_index_set,
    xi_time_part60aca_morita_type_forgets_block_sizes_scalar_count, Omega.X.card_eq_fib]

end Omega.Zeta
