import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Int.Basic
import Mathlib.Tactic
import Omega.Zeta.BooleanBinaryJumpKernelsTensorSpectrum

namespace Omega.Zeta

open scoped BigOperators

/-- The complement involution on Boolean words. -/
def xi_boolean_binary_jump_kernels_dihedral_inversion_complement {q : Nat} (u : Fin q → Bool) :
    Fin q → Bool := fun i => !(u i)

/-- Hamming-parity diagonal entry `(-1)^|u|`, written as a product of coordinate signs. -/
def xi_boolean_binary_jump_kernels_dihedral_inversion_hamming_sign (q : Nat) (u : Fin q → Bool) :
    Int :=
  ∏ i : Fin q, if u i then (-1 : Int) else 1

/-- The `C_q` kernel from the Boolean jump tensor package. -/
def xi_boolean_binary_jump_kernels_dihedral_inversion_C (q : Nat) (u v : Fin q → Bool) : Int :=
  xiBooleanBinaryJumpKernel q u v

/-- The complementary `D_q` kernel obtained by conjugating `C_q` with the complement permutation.
-/
def xi_boolean_binary_jump_kernels_dihedral_inversion_D (q : Nat) (u v : Fin q → Bool) : Int :=
  xi_boolean_binary_jump_kernels_dihedral_inversion_C q
    (xi_boolean_binary_jump_kernels_dihedral_inversion_complement u)
    (xi_boolean_binary_jump_kernels_dihedral_inversion_complement v)

/-- Entrywise inverse-kernel formula for `D_q`. -/
def xi_boolean_binary_jump_kernels_dihedral_inversion_D_inv (q : Nat) (u v : Fin q → Bool) : Int :=
  ((-1 : Int) ^ q) *
    xi_boolean_binary_jump_kernels_dihedral_inversion_hamming_sign q u *
      xi_boolean_binary_jump_kernels_dihedral_inversion_C q u v *
        xi_boolean_binary_jump_kernels_dihedral_inversion_hamming_sign q v

/-- Entrywise inverse-kernel formula for `C_q`. -/
def xi_boolean_binary_jump_kernels_dihedral_inversion_C_inv (q : Nat) (u v : Fin q → Bool) : Int :=
  ((-1 : Int) ^ q) *
    xi_boolean_binary_jump_kernels_dihedral_inversion_hamming_sign q u *
      xi_boolean_binary_jump_kernels_dihedral_inversion_D q u v *
        xi_boolean_binary_jump_kernels_dihedral_inversion_hamming_sign q v

/-- Entrywise form of the complement permutation matrix `P_κ`. -/
def xi_boolean_binary_jump_kernels_dihedral_inversion_P_kappa (q : Nat) (u v : Fin q → Bool) :
    Int :=
  if v = xi_boolean_binary_jump_kernels_dihedral_inversion_complement u then 1 else 0

/-- The full dihedral-inversion package for the Boolean jump kernels. -/
def xi_boolean_binary_jump_kernels_dihedral_inversion_statement (q : Nat) : Prop :=
  (∀ u v : Fin q → Bool,
      xi_boolean_binary_jump_kernels_dihedral_inversion_D_inv q u v =
        ((-1 : Int) ^ q) *
          xi_boolean_binary_jump_kernels_dihedral_inversion_hamming_sign q u *
            xi_boolean_binary_jump_kernels_dihedral_inversion_C q u v *
              xi_boolean_binary_jump_kernels_dihedral_inversion_hamming_sign q v) ∧
    (∀ u v : Fin q → Bool,
      xi_boolean_binary_jump_kernels_dihedral_inversion_C_inv q u v =
        ((-1 : Int) ^ q) *
          xi_boolean_binary_jump_kernels_dihedral_inversion_hamming_sign q u *
            xi_boolean_binary_jump_kernels_dihedral_inversion_D q u v *
              xi_boolean_binary_jump_kernels_dihedral_inversion_hamming_sign q v) ∧
    (∀ u v : Fin q → Bool,
      xi_boolean_binary_jump_kernels_dihedral_inversion_C_inv q u v =
        ((-1 : Int) ^ q) *
          xi_boolean_binary_jump_kernels_dihedral_inversion_hamming_sign q u *
            xi_boolean_binary_jump_kernels_dihedral_inversion_C q
              (xi_boolean_binary_jump_kernels_dihedral_inversion_complement u)
              (xi_boolean_binary_jump_kernels_dihedral_inversion_complement v) *
              xi_boolean_binary_jump_kernels_dihedral_inversion_hamming_sign q v) ∧
    (∀ u : Fin q → Bool,
      xi_boolean_binary_jump_kernels_dihedral_inversion_hamming_sign q
          (xi_boolean_binary_jump_kernels_dihedral_inversion_complement u) =
        ((-1 : Int) ^ q) * xi_boolean_binary_jump_kernels_dihedral_inversion_hamming_sign q u) ∧
    (∀ u : Fin q → Bool,
      ((-1 : Int) ^ q) *
          xi_boolean_binary_jump_kernels_dihedral_inversion_hamming_sign q u *
          xi_boolean_binary_jump_kernels_dihedral_inversion_hamming_sign q
            (xi_boolean_binary_jump_kernels_dihedral_inversion_complement u) =
        1)

lemma xi_boolean_binary_jump_kernels_dihedral_inversion_hamming_sign_complement :
    ∀ q (u : Fin q → Bool),
      xi_boolean_binary_jump_kernels_dihedral_inversion_hamming_sign q
          (xi_boolean_binary_jump_kernels_dihedral_inversion_complement u) =
        ((-1 : Int) ^ q) * xi_boolean_binary_jump_kernels_dihedral_inversion_hamming_sign q u
  | 0, u => by
      simp [xi_boolean_binary_jump_kernels_dihedral_inversion_hamming_sign,
        xi_boolean_binary_jump_kernels_dihedral_inversion_complement]
  | q + 1, u => by
      have htail :=
        xi_boolean_binary_jump_kernels_dihedral_inversion_hamming_sign_complement q
          (fun i => u i.succ)
      have htail' :
          (∏ i : Fin q, if u i.succ = false then -1 else 1) =
            ((-1 : Int) ^ q) * ∏ i : Fin q, if u i.succ = true then -1 else 1 := by
        simpa [xi_boolean_binary_jump_kernels_dihedral_inversion_hamming_sign,
          xi_boolean_binary_jump_kernels_dihedral_inversion_complement] using htail
      cases h0 : u 0
      · simp [xi_boolean_binary_jump_kernels_dihedral_inversion_hamming_sign,
          xi_boolean_binary_jump_kernels_dihedral_inversion_complement, Fin.prod_univ_succ, h0,
          pow_succ, htail', mul_comm]
      · simp [xi_boolean_binary_jump_kernels_dihedral_inversion_hamming_sign,
          xi_boolean_binary_jump_kernels_dihedral_inversion_complement, Fin.prod_univ_succ, h0,
          pow_succ, htail', mul_comm]

lemma xi_boolean_binary_jump_kernels_dihedral_inversion_hamming_sign_sq_one :
    ∀ q (u : Fin q → Bool),
      xi_boolean_binary_jump_kernels_dihedral_inversion_hamming_sign q u *
          xi_boolean_binary_jump_kernels_dihedral_inversion_hamming_sign q u = 1
  | 0, u => by
      simp [xi_boolean_binary_jump_kernels_dihedral_inversion_hamming_sign]
  | q + 1, u => by
      have htail :=
        xi_boolean_binary_jump_kernels_dihedral_inversion_hamming_sign_sq_one q (fun i => u i.succ)
      have htail' :
          ((∏ i : Fin q, if u i.succ = true then -1 else 1) *
              ∏ i : Fin q, if u i.succ = true then -1 else 1) = 1 := by
        simpa [xi_boolean_binary_jump_kernels_dihedral_inversion_hamming_sign] using htail
      cases h0 : u 0
      · simp [xi_boolean_binary_jump_kernels_dihedral_inversion_hamming_sign, Fin.prod_univ_succ,
          h0, htail']
      · simp [xi_boolean_binary_jump_kernels_dihedral_inversion_hamming_sign, Fin.prod_univ_succ,
          h0, htail']

/-- The Boolean jump-kernel inverse package is conjugate to itself through Hamming parity and the
complement involution, and the resulting `H P_κ` involution squares to `(-1)^q` entrywise. -/
theorem paper_xi_boolean_binary_jump_kernels_dihedral_inversion (q : Nat) :
    xi_boolean_binary_jump_kernels_dihedral_inversion_statement q := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro u v
    rfl
  · intro u v
    rfl
  · intro u v
    rfl
  · intro u
    exact xi_boolean_binary_jump_kernels_dihedral_inversion_hamming_sign_complement q u
  · intro u
    rw [xi_boolean_binary_jump_kernels_dihedral_inversion_hamming_sign_complement]
    calc
      ((-1 : Int) ^ q) * xi_boolean_binary_jump_kernels_dihedral_inversion_hamming_sign q u *
          (((-1 : Int) ^ q) * xi_boolean_binary_jump_kernels_dihedral_inversion_hamming_sign q u)
        = (((-1 : Int) ^ q) * ((-1 : Int) ^ q)) *
            (xi_boolean_binary_jump_kernels_dihedral_inversion_hamming_sign q u *
              xi_boolean_binary_jump_kernels_dihedral_inversion_hamming_sign q u) := by ring
      _ = (((-1 : Int) ^ q) * ((-1 : Int) ^ q)) * 1 := by
            rw [xi_boolean_binary_jump_kernels_dihedral_inversion_hamming_sign_sq_one]
      _ = 1 := by
            rw [← pow_add]
            norm_num

end Omega.Zeta
