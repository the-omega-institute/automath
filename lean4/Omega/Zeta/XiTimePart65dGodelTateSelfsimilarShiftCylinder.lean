import Mathlib.Tactic

namespace Omega.Zeta

universe u

/-- Concrete stream model for the Gödel--Tate self-similar cylinder statement.  The
alphabet is the finite event code alphabet; addresses are one-sided streams over it. -/
structure xi_time_part65d_godeltate_selfsimilar_shift_cylinder_Data where
  xi_time_part65d_godeltate_selfsimilar_shift_cylinder_alphabet : Type u

/-- One-sided address streams. -/
def xi_time_part65d_godeltate_selfsimilar_shift_cylinder_Stream
    (D : xi_time_part65d_godeltate_selfsimilar_shift_cylinder_Data) : Type u :=
  Nat → D.xi_time_part65d_godeltate_selfsimilar_shift_cylinder_alphabet

/-- The left shift on address streams. -/
def xi_time_part65d_godeltate_selfsimilar_shift_cylinder_shift
    (D : xi_time_part65d_godeltate_selfsimilar_shift_cylinder_Data)
    (s : xi_time_part65d_godeltate_selfsimilar_shift_cylinder_Stream D) :
    xi_time_part65d_godeltate_selfsimilar_shift_cylinder_Stream D :=
  fun n => s (n + 1)

/-- The inverse branch obtained by adding a first digit. -/
def xi_time_part65d_godeltate_selfsimilar_shift_cylinder_prepend
    (D : xi_time_part65d_godeltate_selfsimilar_shift_cylinder_Data)
    (a : D.xi_time_part65d_godeltate_selfsimilar_shift_cylinder_alphabet)
    (s : xi_time_part65d_godeltate_selfsimilar_shift_cylinder_Stream D) :
    xi_time_part65d_godeltate_selfsimilar_shift_cylinder_Stream D
  | 0 => a
  | n + 1 => s n

/-- The first-digit cylinder. -/
def xi_time_part65d_godeltate_selfsimilar_shift_cylinder_digitCylinder
    (D : xi_time_part65d_godeltate_selfsimilar_shift_cylinder_Data)
    (a : D.xi_time_part65d_godeltate_selfsimilar_shift_cylinder_alphabet)
    (s : xi_time_part65d_godeltate_selfsimilar_shift_cylinder_Stream D) : Prop :=
  s 0 = a

/-- The cylinder with a fixed prefix of length `n`. -/
def xi_time_part65d_godeltate_selfsimilar_shift_cylinder_prefixCylinder
    (D : xi_time_part65d_godeltate_selfsimilar_shift_cylinder_Data) {n : Nat}
    (p : Fin n → D.xi_time_part65d_godeltate_selfsimilar_shift_cylinder_alphabet)
    (s : xi_time_part65d_godeltate_selfsimilar_shift_cylinder_Stream D) : Prop :=
  ∀ i : Fin n, s i.val = p i

lemma xi_time_part65d_godeltate_selfsimilar_shift_cylinder_shift_prepend
    (D : xi_time_part65d_godeltate_selfsimilar_shift_cylinder_Data)
    (a : D.xi_time_part65d_godeltate_selfsimilar_shift_cylinder_alphabet)
    (s : xi_time_part65d_godeltate_selfsimilar_shift_cylinder_Stream D) :
    xi_time_part65d_godeltate_selfsimilar_shift_cylinder_shift D
        (xi_time_part65d_godeltate_selfsimilar_shift_cylinder_prepend D a s) =
      s := by
  rfl

lemma xi_time_part65d_godeltate_selfsimilar_shift_cylinder_prepend_shift
    (D : xi_time_part65d_godeltate_selfsimilar_shift_cylinder_Data)
    (s : xi_time_part65d_godeltate_selfsimilar_shift_cylinder_Stream D) :
    xi_time_part65d_godeltate_selfsimilar_shift_cylinder_prepend D (s 0)
        (xi_time_part65d_godeltate_selfsimilar_shift_cylinder_shift D s) =
      s := by
  funext n
  cases n <;> rfl

/-- Strict one-step first-digit decomposition, including disjointness of digit cylinders. -/
def xi_time_part65d_godeltate_selfsimilar_shift_cylinder_Data.strictSelfSimilar
    (D : xi_time_part65d_godeltate_selfsimilar_shift_cylinder_Data) : Prop :=
  (∀ s : xi_time_part65d_godeltate_selfsimilar_shift_cylinder_Stream D,
      ∃ a t,
        s = xi_time_part65d_godeltate_selfsimilar_shift_cylinder_prepend D a t ∧
          xi_time_part65d_godeltate_selfsimilar_shift_cylinder_digitCylinder D a s) ∧
    ∀ a b s,
      xi_time_part65d_godeltate_selfsimilar_shift_cylinder_digitCylinder D a s →
        xi_time_part65d_godeltate_selfsimilar_shift_cylinder_digitCylinder D b s →
          a = b

/-- The shift is inverse to the first-digit branch and every stream splits as digit plus tail. -/
def xi_time_part65d_godeltate_selfsimilar_shift_cylinder_Data.shiftConjugate
    (D : xi_time_part65d_godeltate_selfsimilar_shift_cylinder_Data) : Prop :=
  (∀ a t,
      xi_time_part65d_godeltate_selfsimilar_shift_cylinder_shift D
          (xi_time_part65d_godeltate_selfsimilar_shift_cylinder_prepend D a t) =
        t) ∧
    ∀ s,
      xi_time_part65d_godeltate_selfsimilar_shift_cylinder_prepend D (s 0)
          (xi_time_part65d_godeltate_selfsimilar_shift_cylinder_shift D s) =
        s

/-- Every stream lies in a unique cylinder for each prefix length. -/
def xi_time_part65d_godeltate_selfsimilar_shift_cylinder_Data.clopenCylinderDecomposition
    (D : xi_time_part65d_godeltate_selfsimilar_shift_cylinder_Data) : Prop :=
  ∀ (n : Nat) (s : xi_time_part65d_godeltate_selfsimilar_shift_cylinder_Stream D),
    ∃ p : Fin n → D.xi_time_part65d_godeltate_selfsimilar_shift_cylinder_alphabet,
      xi_time_part65d_godeltate_selfsimilar_shift_cylinder_prefixCylinder D p s ∧
        ∀ q,
          xi_time_part65d_godeltate_selfsimilar_shift_cylinder_prefixCylinder D q s →
            q = p

/-- Paper label: `thm:xi-time-part65d-godeltate-selfsimilar-shift-cylinder`. -/
theorem paper_xi_time_part65d_godeltate_selfsimilar_shift_cylinder
    (D : xi_time_part65d_godeltate_selfsimilar_shift_cylinder_Data) :
    D.strictSelfSimilar ∧ D.shiftConjugate ∧ D.clopenCylinderDecomposition := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro s
      refine ⟨s 0, xi_time_part65d_godeltate_selfsimilar_shift_cylinder_shift D s, ?_, rfl⟩
      exact (xi_time_part65d_godeltate_selfsimilar_shift_cylinder_prepend_shift D s).symm
    · intro a b s ha hb
      exact ha.symm.trans hb
  · exact ⟨xi_time_part65d_godeltate_selfsimilar_shift_cylinder_shift_prepend D,
      xi_time_part65d_godeltate_selfsimilar_shift_cylinder_prepend_shift D⟩
  · intro n s
    refine ⟨fun i => s i.val, ?_, ?_⟩
    · intro i
      rfl
    · intro q hq
      funext i
      exact (hq i).symm

end Omega.Zeta
