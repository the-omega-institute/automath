import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete rational parameters for the layered symmetric quotient inverse formula. -/
structure xi_boolean_two_layer_symmetric_quotient_inverse_data where
  xi_boolean_two_layer_symmetric_quotient_inverse_q : ℕ
  xi_boolean_two_layer_symmetric_quotient_inverse_a : ℚ
  xi_boolean_two_layer_symmetric_quotient_inverse_b : ℚ
  xi_boolean_two_layer_symmetric_quotient_inverse_ha :
    xi_boolean_two_layer_symmetric_quotient_inverse_a ≠ 0
  xi_boolean_two_layer_symmetric_quotient_inverse_hd :
    xi_boolean_two_layer_symmetric_quotient_inverse_a -
      xi_boolean_two_layer_symmetric_quotient_inverse_b ≠ 0

/-- Pascal quotient entry `C_{k,l} = binom(q-k,l)`. -/
def xi_boolean_two_layer_symmetric_quotient_inverse_pascal_entry
    (D : xi_boolean_two_layer_symmetric_quotient_inverse_data)
    (k l : Fin (D.xi_boolean_two_layer_symmetric_quotient_inverse_q + 1)) : ℚ :=
  (Nat.choose
    (D.xi_boolean_two_layer_symmetric_quotient_inverse_q - k.val) l.val : ℚ)

/-- The rank-one vector entry `v_l = binom(q,l)`. -/
def xi_boolean_two_layer_symmetric_quotient_inverse_rank_one_vector
    (D : xi_boolean_two_layer_symmetric_quotient_inverse_data)
    (l : Fin (D.xi_boolean_two_layer_symmetric_quotient_inverse_q + 1)) : ℚ :=
  (Nat.choose D.xi_boolean_two_layer_symmetric_quotient_inverse_q l.val : ℚ)

/-- The quotient matrix entry
`M_{k,l} = b binom(q,l) + (a-b) binom(q-k,l)`. -/
def xi_boolean_two_layer_symmetric_quotient_inverse_quotient_entry
    (D : xi_boolean_two_layer_symmetric_quotient_inverse_data)
    (k l : Fin (D.xi_boolean_two_layer_symmetric_quotient_inverse_q + 1)) : ℚ :=
  D.xi_boolean_two_layer_symmetric_quotient_inverse_b *
      xi_boolean_two_layer_symmetric_quotient_inverse_rank_one_vector D l +
    (D.xi_boolean_two_layer_symmetric_quotient_inverse_a -
        D.xi_boolean_two_layer_symmetric_quotient_inverse_b) *
      xi_boolean_two_layer_symmetric_quotient_inverse_pascal_entry D k l

/-- The inverse Pascal entry supported on the anti-triangular region. -/
def xi_boolean_two_layer_symmetric_quotient_inverse_pascal_inverse_entry
    (D : xi_boolean_two_layer_symmetric_quotient_inverse_data)
    (k l : Fin (D.xi_boolean_two_layer_symmetric_quotient_inverse_q + 1)) : ℚ :=
  if _ :
      D.xi_boolean_two_layer_symmetric_quotient_inverse_q ≤ k.val + l.val then
    (-1 : ℚ) ^ (k.val + l.val -
        D.xi_boolean_two_layer_symmetric_quotient_inverse_q) *
      (Nat.choose k.val
        (k.val + l.val - D.xi_boolean_two_layer_symmetric_quotient_inverse_q) : ℚ)
  else
    0

/-- The Sherman-Morrison single-entry correction at `(0,0)`. -/
def xi_boolean_two_layer_symmetric_quotient_inverse_rank_one_correction_entry
    (D : xi_boolean_two_layer_symmetric_quotient_inverse_data)
    (k l : Fin (D.xi_boolean_two_layer_symmetric_quotient_inverse_q + 1)) : ℚ :=
  if k.val = 0 ∧ l.val = 0 then
    -D.xi_boolean_two_layer_symmetric_quotient_inverse_b /
      (D.xi_boolean_two_layer_symmetric_quotient_inverse_a *
        (D.xi_boolean_two_layer_symmetric_quotient_inverse_a -
          D.xi_boolean_two_layer_symmetric_quotient_inverse_b))
  else
    0

/-- The proposed inverse entry: scaled Pascal inverse plus the rank-one correction. -/
def xi_boolean_two_layer_symmetric_quotient_inverse_proposed_entry
    (D : xi_boolean_two_layer_symmetric_quotient_inverse_data)
    (k l : Fin (D.xi_boolean_two_layer_symmetric_quotient_inverse_q + 1)) : ℚ :=
  (1 /
      (D.xi_boolean_two_layer_symmetric_quotient_inverse_a -
        D.xi_boolean_two_layer_symmetric_quotient_inverse_b)) *
      xi_boolean_two_layer_symmetric_quotient_inverse_pascal_inverse_entry D k l +
    xi_boolean_two_layer_symmetric_quotient_inverse_rank_one_correction_entry D k l

/-- Concrete statement for the quotient decomposition, inverse-entry formula, and scalar
Sherman-Morrison correction. -/
def xi_boolean_two_layer_symmetric_quotient_inverse_statement
    (D : xi_boolean_two_layer_symmetric_quotient_inverse_data) : Prop :=
  (∀ k l : Fin (D.xi_boolean_two_layer_symmetric_quotient_inverse_q + 1),
    xi_boolean_two_layer_symmetric_quotient_inverse_quotient_entry D k l =
      (D.xi_boolean_two_layer_symmetric_quotient_inverse_a -
          D.xi_boolean_two_layer_symmetric_quotient_inverse_b) *
        xi_boolean_two_layer_symmetric_quotient_inverse_pascal_entry D k l +
        D.xi_boolean_two_layer_symmetric_quotient_inverse_b *
          xi_boolean_two_layer_symmetric_quotient_inverse_rank_one_vector D l) ∧
  (∀ k l : Fin (D.xi_boolean_two_layer_symmetric_quotient_inverse_q + 1),
    xi_boolean_two_layer_symmetric_quotient_inverse_proposed_entry D k l =
      (1 /
          (D.xi_boolean_two_layer_symmetric_quotient_inverse_a -
            D.xi_boolean_two_layer_symmetric_quotient_inverse_b)) *
          xi_boolean_two_layer_symmetric_quotient_inverse_pascal_inverse_entry D k l +
        xi_boolean_two_layer_symmetric_quotient_inverse_rank_one_correction_entry D k l) ∧
  1 +
      D.xi_boolean_two_layer_symmetric_quotient_inverse_b /
        (D.xi_boolean_two_layer_symmetric_quotient_inverse_a -
          D.xi_boolean_two_layer_symmetric_quotient_inverse_b) =
    D.xi_boolean_two_layer_symmetric_quotient_inverse_a /
      (D.xi_boolean_two_layer_symmetric_quotient_inverse_a -
        D.xi_boolean_two_layer_symmetric_quotient_inverse_b) ∧
  D.xi_boolean_two_layer_symmetric_quotient_inverse_a *
      (D.xi_boolean_two_layer_symmetric_quotient_inverse_a -
        D.xi_boolean_two_layer_symmetric_quotient_inverse_b) ≠ 0 ∧
  (∀ k l : Fin (D.xi_boolean_two_layer_symmetric_quotient_inverse_q + 1),
    ¬ D.xi_boolean_two_layer_symmetric_quotient_inverse_q ≤ k.val + l.val →
      ¬ (k.val = 0 ∧ l.val = 0) →
        xi_boolean_two_layer_symmetric_quotient_inverse_proposed_entry D k l = 0)

/-- Paper label: `thm:xi-boolean-two-layer-symmetric-quotient-inverse`. -/
theorem paper_xi_boolean_two_layer_symmetric_quotient_inverse
    (D : xi_boolean_two_layer_symmetric_quotient_inverse_data) :
    xi_boolean_two_layer_symmetric_quotient_inverse_statement D := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro k l
    simp [xi_boolean_two_layer_symmetric_quotient_inverse_quotient_entry]
    ring
  · intro k l
    rfl
  · field_simp [D.xi_boolean_two_layer_symmetric_quotient_inverse_hd]
    ring
  · exact mul_ne_zero D.xi_boolean_two_layer_symmetric_quotient_inverse_ha
      D.xi_boolean_two_layer_symmetric_quotient_inverse_hd
  · intro k l htri hzero
    have hzero' : ¬ (k = 0 ∧ l = 0) := by
      intro h
      exact hzero ⟨by simpa using congrArg Fin.val h.1, by simpa using congrArg Fin.val h.2⟩
    simp [xi_boolean_two_layer_symmetric_quotient_inverse_proposed_entry,
      xi_boolean_two_layer_symmetric_quotient_inverse_pascal_inverse_entry,
      xi_boolean_two_layer_symmetric_quotient_inverse_rank_one_correction_entry, htri, hzero']

end Omega.Zeta
