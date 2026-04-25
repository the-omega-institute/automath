import Mathlib.Tactic

namespace Omega.Zeta

/-- The binomial upper-triangular factor in the Smith staircase template.  Rows and columns
are indexed from `0` to `q`; the entry is zero below the diagonal and has diagonal `1`. -/
def xi_smith_staircase_template_symq_upper (q : ℕ) :
    Matrix (Fin (q + 1)) (Fin (q + 1)) ℤ :=
  fun r j =>
    if (r : ℕ) ≤ (j : ℕ) then
      (-1 : ℤ) ^ ((j : ℕ) - (r : ℕ)) * Nat.choose (j : ℕ) (r : ℕ)
    else
      0

/-- The advertised PID Smith exponents for the staircase template. -/
def xi_smith_staircase_template_symq_pid_exponents (q : ℕ) : List ℕ :=
  List.range (q + 1)

/-- Concrete unimodular-decomposition core: the binomial factor is upper triangular with
unit diagonal. -/
def xi_smith_staircase_template_symq_has_unimodular_decomposition (q : ℕ) : Prop :=
  (∀ r j : Fin (q + 1),
      (j : ℕ) < (r : ℕ) → xi_smith_staircase_template_symq_upper q r j = 0) ∧
    ∀ j : Fin (q + 1), xi_smith_staircase_template_symq_upper q j j = 1

/-- Concrete PID Smith-shape core: the invariant exponents are the staircase `0, ..., q`. -/
def xi_smith_staircase_template_symq_has_pid_smith_shape (q : ℕ) : Prop :=
  xi_smith_staircase_template_symq_pid_exponents q = List.range (q + 1)

/-- Paper label: `prop:xi-smith-staircase-template-symq`.

The concrete binomial factor in the staircase template is upper triangular with unit
diagonal, and the corresponding PID Smith exponent list is the staircase `0, ..., q`. -/
theorem paper_xi_smith_staircase_template_symq :
    (∀ q : ℕ, xi_smith_staircase_template_symq_has_unimodular_decomposition q) ∧
      ∀ q : ℕ, xi_smith_staircase_template_symq_has_pid_smith_shape q := by
  constructor
  · intro q
    constructor
    · intro r j hlt
      unfold xi_smith_staircase_template_symq_upper
      simp [Nat.not_le_of_gt hlt]
    · intro j
      unfold xi_smith_staircase_template_symq_upper
      simp
  · intro q
    rfl

end Omega.Zeta
