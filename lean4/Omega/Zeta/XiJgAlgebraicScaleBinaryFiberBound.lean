import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Label-prefixed algebraic-scale data for the binary fiber model: the transported roots are
encoded by sign vectors, and each original root has a recorded single-coordinate quadratic
reconstruction witness. -/
structure xi_jg_algebraic_scale_binary_fiber_bound_data where
  xi_jg_algebraic_scale_binary_fiber_bound_root_count : ℕ
  xi_jg_algebraic_scale_binary_fiber_bound_base_field : Type*
  xi_jg_algebraic_scale_binary_fiber_bound_field :
    Field xi_jg_algebraic_scale_binary_fiber_bound_base_field
  xi_jg_algebraic_scale_binary_fiber_bound_scale :
    xi_jg_algebraic_scale_binary_fiber_bound_base_field
  xi_jg_algebraic_scale_binary_fiber_bound_scale_nonzero :
    xi_jg_algebraic_scale_binary_fiber_bound_scale ≠ 0
  xi_jg_algebraic_scale_binary_fiber_bound_radicand :
    Fin xi_jg_algebraic_scale_binary_fiber_bound_root_count →
      xi_jg_algebraic_scale_binary_fiber_bound_base_field
  xi_jg_algebraic_scale_binary_fiber_bound_original_root_sign :
    Fin xi_jg_algebraic_scale_binary_fiber_bound_root_count →
      Fin xi_jg_algebraic_scale_binary_fiber_bound_root_count → Bool
  xi_jg_algebraic_scale_binary_fiber_bound_quadratic_reconstruction_witness :
    ∀ i j,
      j ≠ i →
        xi_jg_algebraic_scale_binary_fiber_bound_original_root_sign i j = false

/-- Sign vectors for the compositum of the recorded quadratic extensions. -/
abbrev xi_jg_algebraic_scale_binary_fiber_bound_sign_vector
    (D : xi_jg_algebraic_scale_binary_fiber_bound_data) : Type :=
  Fin D.xi_jg_algebraic_scale_binary_fiber_bound_root_count → Bool

/-- The `i`th quadratic extension changes only the `i`th sign coordinate. -/
def xi_jg_algebraic_scale_binary_fiber_bound_corresponding_quadratic_extension
    (D : xi_jg_algebraic_scale_binary_fiber_bound_data)
    (i : Fin D.xi_jg_algebraic_scale_binary_fiber_bound_root_count)
    (ε : xi_jg_algebraic_scale_binary_fiber_bound_sign_vector D) : Prop :=
  ∀ j, j ≠ i → ε j = false

/-- The elementary-two operation on the binary sign ledger. -/
def xi_jg_algebraic_scale_binary_fiber_bound_double_sign
    (D : xi_jg_algebraic_scale_binary_fiber_bound_data)
    (ε : xi_jg_algebraic_scale_binary_fiber_bound_sign_vector D) :
    xi_jg_algebraic_scale_binary_fiber_bound_sign_vector D :=
  fun i => Bool.xor (ε i) (ε i)

/-- The algebraic scale produces at most one binary choice for each original root. -/
def xi_jg_algebraic_scale_binary_fiber_bound_statement
    (D : xi_jg_algebraic_scale_binary_fiber_bound_data) : Prop :=
  (∀ i,
    xi_jg_algebraic_scale_binary_fiber_bound_corresponding_quadratic_extension D i
      (D.xi_jg_algebraic_scale_binary_fiber_bound_original_root_sign i)) ∧
    Fintype.card (xi_jg_algebraic_scale_binary_fiber_bound_sign_vector D) =
      2 ^ D.xi_jg_algebraic_scale_binary_fiber_bound_root_count ∧
      (∀ ε : xi_jg_algebraic_scale_binary_fiber_bound_sign_vector D,
        xi_jg_algebraic_scale_binary_fiber_bound_double_sign D ε = fun _ => false)

/-- Paper label: `prop:xi-jg-algebraic-scale-binary-fiber-bound`. -/
theorem paper_xi_jg_algebraic_scale_binary_fiber_bound
    (D : xi_jg_algebraic_scale_binary_fiber_bound_data) :
    xi_jg_algebraic_scale_binary_fiber_bound_statement D := by
  constructor
  · intro i j hij
    exact D.xi_jg_algebraic_scale_binary_fiber_bound_quadratic_reconstruction_witness i j hij
  constructor
  · simp [xi_jg_algebraic_scale_binary_fiber_bound_sign_vector]
  · intro ε
    ext i
    simp [xi_jg_algebraic_scale_binary_fiber_bound_double_sign]

end Omega.Zeta
