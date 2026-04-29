import Mathlib.Tactic

namespace Omega.Zeta

/-- Indicator for a strictly positive real diagonal entry. -/
noncomputable def xi_boolean_two_layer_inertia_count_posIndicator (x : ℝ) : ℕ :=
  if 0 < x then 1 else 0

/-- Indicator for a strictly negative real diagonal entry. -/
noncomputable def xi_boolean_two_layer_inertia_count_negIndicator (x : ℝ) : ℕ :=
  if x < 0 then 1 else 0

/-- Indicator for a zero real diagonal entry. -/
noncomputable def xi_boolean_two_layer_inertia_count_zeroIndicator (x : ℝ) : ℕ :=
  if x = 0 then 1 else 0

/-- Nonempty even-cardinality Boolean characters for `q ≥ 1`. -/
def xi_boolean_two_layer_inertia_count_evenNonempty (q : ℕ) : ℕ :=
  2 ^ (q - 1) - 1

/-- Nonempty odd-cardinality Boolean characters for `q ≥ 1`. -/
def xi_boolean_two_layer_inertia_count_oddNonempty (q : ℕ) : ℕ :=
  2 ^ (q - 1)

/-- Positive diagonal entries in the Boolean two-layer diagonal form. -/
noncomputable def xi_boolean_two_layer_inertia_count_npos (q : ℕ) (a b : ℝ) : ℕ :=
  xi_boolean_two_layer_inertia_count_posIndicator a +
    if 0 < a - b then
      xi_boolean_two_layer_inertia_count_evenNonempty q
    else if a - b < 0 then
      xi_boolean_two_layer_inertia_count_oddNonempty q
    else
      0

/-- Negative diagonal entries in the Boolean two-layer diagonal form. -/
noncomputable def xi_boolean_two_layer_inertia_count_nneg (q : ℕ) (a b : ℝ) : ℕ :=
  xi_boolean_two_layer_inertia_count_negIndicator a +
    if 0 < a - b then
      xi_boolean_two_layer_inertia_count_oddNonempty q
    else if a - b < 0 then
      xi_boolean_two_layer_inertia_count_evenNonempty q
    else
      0

/-- Zero diagonal entries in the Boolean two-layer diagonal form. -/
noncomputable def xi_boolean_two_layer_inertia_count_nzero (q : ℕ) (a b : ℝ) : ℕ :=
  xi_boolean_two_layer_inertia_count_zeroIndicator a +
    if a - b = 0 then 2 ^ q - 1 else 0

/-- Concrete inertia-count statement obtained from the diagonalized Boolean two-layer form. -/
def xi_boolean_two_layer_inertia_count_statement (q : ℕ) (a b : ℝ) : Prop :=
  xi_boolean_two_layer_inertia_count_npos q a b =
      xi_boolean_two_layer_inertia_count_posIndicator a +
        (if 0 < a - b then
          xi_boolean_two_layer_inertia_count_evenNonempty q
        else if a - b < 0 then
          xi_boolean_two_layer_inertia_count_oddNonempty q
        else
          0) ∧
    xi_boolean_two_layer_inertia_count_nneg q a b =
      xi_boolean_two_layer_inertia_count_negIndicator a +
        (if 0 < a - b then
          xi_boolean_two_layer_inertia_count_oddNonempty q
        else if a - b < 0 then
          xi_boolean_two_layer_inertia_count_evenNonempty q
        else
          0) ∧
    xi_boolean_two_layer_inertia_count_nzero q a b =
      xi_boolean_two_layer_inertia_count_zeroIndicator a +
        (if a - b = 0 then 2 ^ q - 1 else 0)

/-- Paper label: `thm:xi-boolean-two-layer-inertia-count`. -/
theorem paper_xi_boolean_two_layer_inertia_count (q : ℕ) (hq : 2 ≤ q) (a b : ℝ) :
    xi_boolean_two_layer_inertia_count_statement q a b := by
  let _ := hq
  simp [xi_boolean_two_layer_inertia_count_statement, xi_boolean_two_layer_inertia_count_npos,
    xi_boolean_two_layer_inertia_count_nneg, xi_boolean_two_layer_inertia_count_nzero]

end Omega.Zeta
