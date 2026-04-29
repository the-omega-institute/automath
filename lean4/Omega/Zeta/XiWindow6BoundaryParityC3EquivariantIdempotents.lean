import Mathlib

namespace Omega.Zeta

/-- The three boundary parity coordinates, with coefficients in `𝔽₂`. -/
abbrev xi_window6_boundary_parity_c3_equivariant_idempotents_module :=
  ZMod 2 × ZMod 2 × ZMod 2

/-- Cyclic convolution in the group algebra `𝔽₂[C₃]`, written on coefficient triples. -/
def xi_window6_boundary_parity_c3_equivariant_idempotents_mul
    (a b : xi_window6_boundary_parity_c3_equivariant_idempotents_module) :
    xi_window6_boundary_parity_c3_equivariant_idempotents_module :=
  (a.1 * b.1 + a.2.1 * b.2.2 + a.2.2 * b.2.1,
    a.1 * b.2.1 + a.2.1 * b.1 + a.2.2 * b.2.2,
      a.1 * b.2.2 + a.2.1 * b.2.1 + a.2.2 * b.1)

/-- The cyclic generator `t` acts by rotating the three boundary coordinates. -/
def xi_window6_boundary_parity_c3_equivariant_idempotents_shift
    (a : xi_window6_boundary_parity_c3_equivariant_idempotents_module) :
    xi_window6_boundary_parity_c3_equivariant_idempotents_module :=
  (a.2.1, a.2.2, a.1)

/-- Idempotents in the finite group algebra model. -/
def xi_window6_boundary_parity_c3_equivariant_idempotents_isIdempotent
    (a : xi_window6_boundary_parity_c3_equivariant_idempotents_module) : Prop :=
  xi_window6_boundary_parity_c3_equivariant_idempotents_mul a a = a

/-- The zero idempotent. -/
def xi_window6_boundary_parity_c3_equivariant_idempotents_zero :
    xi_window6_boundary_parity_c3_equivariant_idempotents_module :=
  (0, 0, 0)

/-- The unit idempotent. -/
def xi_window6_boundary_parity_c3_equivariant_idempotents_one :
    xi_window6_boundary_parity_c3_equivariant_idempotents_module :=
  (1, 0, 0)

/-- The nontrivial idempotent supported on `t + t²`. -/
def xi_window6_boundary_parity_c3_equivariant_idempotents_boundary :
    xi_window6_boundary_parity_c3_equivariant_idempotents_module :=
  (0, 1, 1)

/-- The augmentation idempotent `1 + t + t²`. -/
def xi_window6_boundary_parity_c3_equivariant_idempotents_augmentation :
    xi_window6_boundary_parity_c3_equivariant_idempotents_module :=
  (1, 1, 1)

/-- Concrete paper-facing statement: the C₃-equivariant endomorphism algebra is represented by the
finite group algebra coefficients, and its idempotents are exactly the four CRT idempotents. -/
def xi_window6_boundary_parity_c3_equivariant_idempotents_statement : Prop :=
  (∀ a : xi_window6_boundary_parity_c3_equivariant_idempotents_module,
    xi_window6_boundary_parity_c3_equivariant_idempotents_isIdempotent a ↔
      a = xi_window6_boundary_parity_c3_equivariant_idempotents_zero ∨
        a = xi_window6_boundary_parity_c3_equivariant_idempotents_one ∨
          a = xi_window6_boundary_parity_c3_equivariant_idempotents_boundary ∨
            a = xi_window6_boundary_parity_c3_equivariant_idempotents_augmentation) ∧
    (∀ a : xi_window6_boundary_parity_c3_equivariant_idempotents_module,
      (xi_window6_boundary_parity_c3_equivariant_idempotents_shift^[3]) a = a)

private lemma xi_window6_boundary_parity_c3_equivariant_idempotents_idempotent_iff
    (a : xi_window6_boundary_parity_c3_equivariant_idempotents_module) :
    xi_window6_boundary_parity_c3_equivariant_idempotents_isIdempotent a ↔
      a.2.1 = a.2.2 := by
  rcases a with ⟨x, y, z⟩
  fin_cases x <;> fin_cases y <;> fin_cases z <;>
    simp [xi_window6_boundary_parity_c3_equivariant_idempotents_isIdempotent,
      xi_window6_boundary_parity_c3_equivariant_idempotents_mul] <;>
    norm_num <;>
    decide

private lemma xi_window6_boundary_parity_c3_equivariant_idempotents_enumerate
    (a : xi_window6_boundary_parity_c3_equivariant_idempotents_module) :
    a.2.1 = a.2.2 ↔
      a = xi_window6_boundary_parity_c3_equivariant_idempotents_zero ∨
        a = xi_window6_boundary_parity_c3_equivariant_idempotents_one ∨
          a = xi_window6_boundary_parity_c3_equivariant_idempotents_boundary ∨
            a = xi_window6_boundary_parity_c3_equivariant_idempotents_augmentation := by
  rcases a with ⟨x, y, z⟩
  fin_cases x <;> fin_cases y <;> fin_cases z <;>
    simp [xi_window6_boundary_parity_c3_equivariant_idempotents_zero,
      xi_window6_boundary_parity_c3_equivariant_idempotents_one,
      xi_window6_boundary_parity_c3_equivariant_idempotents_boundary,
      xi_window6_boundary_parity_c3_equivariant_idempotents_augmentation]

private lemma xi_window6_boundary_parity_c3_equivariant_idempotents_shift_three
    (a : xi_window6_boundary_parity_c3_equivariant_idempotents_module) :
    (xi_window6_boundary_parity_c3_equivariant_idempotents_shift^[3]) a = a := by
  rcases a with ⟨x, y, z⟩
  rfl

/-- Paper label:
`thm:xi-window6-boundary-parity-c3-equivariant-idempotents`. -/
theorem paper_xi_window6_boundary_parity_c3_equivariant_idempotents :
    xi_window6_boundary_parity_c3_equivariant_idempotents_statement := by
  refine ⟨?_, xi_window6_boundary_parity_c3_equivariant_idempotents_shift_three⟩
  intro a
  exact (xi_window6_boundary_parity_c3_equivariant_idempotents_idempotent_iff a).trans
    (xi_window6_boundary_parity_c3_equivariant_idempotents_enumerate a)

end Omega.Zeta
