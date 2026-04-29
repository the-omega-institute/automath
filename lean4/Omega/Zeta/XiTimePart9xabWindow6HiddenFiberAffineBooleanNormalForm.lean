import Mathlib.Tactic

namespace Omega.Zeta

/-- Boolean square used in the window-`6` hidden-fiber normal form. -/
abbrev xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form_boolSquare :=
  Bool × Bool

/-- The affine beta offset `21 a + 34 b` on the Boolean square. -/
def xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form_beta
    (u : xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form_boolSquare) : ℤ :=
  (if u.1 then 21 else 0) + if u.2 then 34 else 0

/-- The two-point Boolean ideal for the `d = 2` staircase case. -/
def xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form_I2 :
    Finset xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form_boolSquare :=
  {(false, false), (false, true)}

/-- The three-point Boolean ideal for the `d = 3` staircase case. -/
def xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form_I3 :
    Finset xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form_boolSquare :=
  {(false, false), (true, false), (false, true)}

/-- The full Boolean square for the `d = 4` staircase case. -/
def xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form_I4 :
    Finset xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form_boolSquare :=
  Finset.univ

/-- Product order on the Boolean square. -/
def xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form_le
    (u v : xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form_boolSquare) : Prop :=
  (u.1 = true → v.1 = true) ∧ (u.2 = true → v.2 = true)

/-- Down-closedness for Boolean ideals in the product order. -/
def xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form_downClosed
    (I : Finset xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form_boolSquare) :
    Prop :=
  ∀ u v, u ∈ I →
    xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form_le v u → v ∈ I

/-- The staircase-classification choice of Boolean ideal for `d = 2,3,4`. -/
def xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form_idealForDim
    (d : ℕ) :
    Finset xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form_boolSquare :=
  if d = 2 then
    xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form_I2
  else if d = 3 then
    xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form_I3
  else
    xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form_I4

/-- The affine hidden fiber above a visible base point. -/
def xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form_hiddenFiber
    (base : ℤ) (d : ℕ) : Finset ℤ :=
  (xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form_idealForDim d).image
    (fun u => base + xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form_beta u)

private lemma xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form_downClosed_I2 :
    xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form_downClosed
      xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form_I2 := by
  intro u v hu huv
  rcases u with ⟨ua, ub⟩
  rcases v with ⟨va, vb⟩
  fin_cases ua <;> fin_cases ub <;> fin_cases va <;> fin_cases vb <;>
    simp [xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form_I2,
      xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form_le] at hu huv ⊢

private lemma xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form_downClosed_I3 :
    xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form_downClosed
      xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form_I3 := by
  intro u v hu huv
  rcases u with ⟨ua, ub⟩
  rcases v with ⟨va, vb⟩
  fin_cases ua <;> fin_cases ub <;> fin_cases va <;> fin_cases vb <;>
    simp [xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form_I3,
      xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form_le] at hu huv ⊢

private lemma xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form_downClosed_I4 :
    xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form_downClosed
      xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form_I4 := by
  intro u v hu huv
  simp [xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form_I4]

/-- Concrete statement for
`thm:xi-time-part9xab-window6-hidden-fiber-affine-boolean-normal-form`: the three staircase cases
have the advertised beta-offset images, and all three indexing sets are product-order ideals. -/
def xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form_statement : Prop :=
  (∀ base : ℤ,
      xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form_hiddenFiber base 2 =
        ({base, base + 34} : Finset ℤ)) ∧
    (∀ base : ℤ,
      xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form_hiddenFiber base 3 =
        ({base, base + 21, base + 34} : Finset ℤ)) ∧
    (∀ base : ℤ,
      xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form_hiddenFiber base 4 =
        ({base, base + 21, base + 34, base + 55} : Finset ℤ)) ∧
    xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form_downClosed
      xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form_I2 ∧
    xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form_downClosed
      xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form_I3 ∧
    xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form_downClosed
      xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form_I4

/-- Paper label:
`thm:xi-time-part9xab-window6-hidden-fiber-affine-boolean-normal-form`. -/
theorem paper_xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form :
    xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form_statement := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro base
    ext x
    simp [xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form_hiddenFiber,
      xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form_idealForDim,
      xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form_I2,
      xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form_beta]
  · intro base
    ext x
    simp [xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form_hiddenFiber,
      xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form_idealForDim,
      xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form_I3,
      xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form_beta]
  · intro base
    ext x
    simp [xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form_hiddenFiber,
      xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form_idealForDim,
      xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form_I4,
      xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form_beta]
    constructor <;> intro h <;> omega
  · exact xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form_downClosed_I2
  · exact xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form_downClosed_I3
  · exact xi_time_part9xab_window6_hidden_fiber_affine_boolean_normal_form_downClosed_I4

end Omega.Zeta
