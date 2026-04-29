import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete Smith self-square-root parameters for the two-endpoint exponent model. -/
structure xi_smith_spectrum_self_square_root_symmetry_data where
  q : ℕ

/-- Endpoint Smith exponent multiset for the self-square-root seed model. -/
def xi_smith_spectrum_self_square_root_symmetry_exponents
    (D : xi_smith_spectrum_self_square_root_symmetry_data) : List ℕ :=
  [0, D.q]

/-- Complement involution on Smith exponents. -/
def xi_smith_spectrum_self_square_root_symmetry_complement
    (D : xi_smith_spectrum_self_square_root_symmetry_data) (r : ℕ) : ℕ :=
  D.q - r

/-- Sorted Smith exponent list. -/
def xi_smith_spectrum_self_square_root_symmetry_sorted
    (D : xi_smith_spectrum_self_square_root_symmetry_data) : List ℕ :=
  (xi_smith_spectrum_self_square_root_symmetry_exponents D).mergeSort (· ≤ ·)

/-- Paper-facing statement for self-square-root Smith exponent complementarity. -/
def xi_smith_spectrum_self_square_root_symmetry_statement
    (D : xi_smith_spectrum_self_square_root_symmetry_data) : Prop :=
  List.Perm
    ((xi_smith_spectrum_self_square_root_symmetry_exponents D).map
      (xi_smith_spectrum_self_square_root_symmetry_complement D))
    (xi_smith_spectrum_self_square_root_symmetry_exponents D) ∧
  xi_smith_spectrum_self_square_root_symmetry_sorted D = [0, D.q] ∧
  (∀ r, r ∈ xi_smith_spectrum_self_square_root_symmetry_exponents D →
    xi_smith_spectrum_self_square_root_symmetry_complement D r ∈
      xi_smith_spectrum_self_square_root_symmetry_exponents D) ∧
  (0 + D.q = D.q ∧ D.q + 0 = D.q)

/-- Paper label: `cor:xi-smith-spectrum-self-square-root-symmetry`. -/
theorem paper_xi_smith_spectrum_self_square_root_symmetry
    (D : xi_smith_spectrum_self_square_root_symmetry_data) :
    xi_smith_spectrum_self_square_root_symmetry_statement D := by
  refine ⟨?_, ?_, ?_, by simp⟩
  · simpa [xi_smith_spectrum_self_square_root_symmetry_exponents,
      xi_smith_spectrum_self_square_root_symmetry_complement] using
      (List.Perm.swap D.q 0 []).symm
  · have hpair : List.Pairwise (fun a b : ℕ => a ≤ b) [0, D.q] := by simp
    simpa [xi_smith_spectrum_self_square_root_symmetry_sorted,
      xi_smith_spectrum_self_square_root_symmetry_exponents] using
      (List.mergeSort_eq_self (r := fun a b : ℕ => a ≤ b) hpair)
  · intro r hr
    simp [xi_smith_spectrum_self_square_root_symmetry_exponents] at hr ⊢
    rcases hr with rfl | rfl <;> simp [xi_smith_spectrum_self_square_root_symmetry_complement]

end Omega.Zeta
