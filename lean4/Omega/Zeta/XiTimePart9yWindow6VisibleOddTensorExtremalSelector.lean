import Mathlib.Tactic

namespace Omega.Zeta

/-- A concrete integer vector in the `B₃` window-`6` root dictionary. -/
def xi_time_part9y_window6_visible_odd_tensor_extremal_selector_vec
    (a b c : ℤ) : Fin 3 → ℤ :=
  ![a, b, c]

/-- The shell with visible binary degree `2`: `{-e₁} ∪ {(0, ±1, ±1)}`. -/
def xi_time_part9y_window6_visible_odd_tensor_extremal_selector_shell2 :
    List (Fin 3 → ℤ) :=
  [xi_time_part9y_window6_visible_odd_tensor_extremal_selector_vec (-1) 0 0,
    xi_time_part9y_window6_visible_odd_tensor_extremal_selector_vec 0 1 1,
    xi_time_part9y_window6_visible_odd_tensor_extremal_selector_vec 0 1 (-1),
    xi_time_part9y_window6_visible_odd_tensor_extremal_selector_vec 0 (-1) 1,
    xi_time_part9y_window6_visible_odd_tensor_extremal_selector_vec 0 (-1) (-1)]

/-- The middle visible shell with binary degree `3`: `{(±1, 0, ±1)}`. -/
def xi_time_part9y_window6_visible_odd_tensor_extremal_selector_shell3 :
    List (Fin 3 → ℤ) :=
  [xi_time_part9y_window6_visible_odd_tensor_extremal_selector_vec 1 0 1,
    xi_time_part9y_window6_visible_odd_tensor_extremal_selector_vec 1 0 (-1),
    xi_time_part9y_window6_visible_odd_tensor_extremal_selector_vec (-1) 0 1,
    xi_time_part9y_window6_visible_odd_tensor_extremal_selector_vec (-1) 0 (-1)]

/-- The shell with visible binary degree `4`: `{e₁, ±e₂, ±e₃} ∪ {(±1, ±1, 0)}`. -/
def xi_time_part9y_window6_visible_odd_tensor_extremal_selector_shell4 :
    List (Fin 3 → ℤ) :=
  [xi_time_part9y_window6_visible_odd_tensor_extremal_selector_vec 1 0 0,
    xi_time_part9y_window6_visible_odd_tensor_extremal_selector_vec 0 1 0,
    xi_time_part9y_window6_visible_odd_tensor_extremal_selector_vec 0 (-1) 0,
    xi_time_part9y_window6_visible_odd_tensor_extremal_selector_vec 0 0 1,
    xi_time_part9y_window6_visible_odd_tensor_extremal_selector_vec 0 0 (-1),
    xi_time_part9y_window6_visible_odd_tensor_extremal_selector_vec 1 1 0,
    xi_time_part9y_window6_visible_odd_tensor_extremal_selector_vec 1 (-1) 0,
    xi_time_part9y_window6_visible_odd_tensor_extremal_selector_vec (-1) 1 0,
    xi_time_part9y_window6_visible_odd_tensor_extremal_selector_vec (-1) (-1) 0]

/-- The complete finite `B₃` root shell partition used by the selector. -/
def xi_time_part9y_window6_visible_odd_tensor_extremal_selector_roots :
    List (Fin 3 → ℤ) :=
  xi_time_part9y_window6_visible_odd_tensor_extremal_selector_shell2 ++
    xi_time_part9y_window6_visible_odd_tensor_extremal_selector_shell3 ++
      xi_time_part9y_window6_visible_odd_tensor_extremal_selector_shell4

/-- The selected Cartan axis `e₁`. -/
def xi_time_part9y_window6_visible_odd_tensor_extremal_selector_axis (i : Fin 3) : ℤ :=
  ![(1 : ℤ), 0, 0] i

/-- The shell-weighted one-fold odd moment. -/
def xi_time_part9y_window6_visible_odd_tensor_extremal_selector_one_fold_sum
    (f : ℤ → ℤ) (i : Fin 3) : ℤ :=
  (xi_time_part9y_window6_visible_odd_tensor_extremal_selector_shell2.map
      (fun β => f 2 * β i)).sum +
    (xi_time_part9y_window6_visible_odd_tensor_extremal_selector_shell3.map
      (fun β => f 3 * β i)).sum +
      (xi_time_part9y_window6_visible_odd_tensor_extremal_selector_shell4.map
        (fun β => f 4 * β i)).sum

/-- The shell-weighted cubic odd tensor moment. -/
def xi_time_part9y_window6_visible_odd_tensor_extremal_selector_cubic_tensor_sum
    (f : ℤ → ℤ) (i j k : Fin 3) : ℤ :=
  (xi_time_part9y_window6_visible_odd_tensor_extremal_selector_shell2.map
      (fun β => f 2 * β i * β j * β k)).sum +
    (xi_time_part9y_window6_visible_odd_tensor_extremal_selector_shell3.map
      (fun β => f 3 * β i * β j * β k)).sum +
      (xi_time_part9y_window6_visible_odd_tensor_extremal_selector_shell4.map
        (fun β => f 4 * β i * β j * β k)).sum

/-- Concrete statement for
`thm:xi-time-part9y-window6-visible-odd-tensor-extremal-selector`. -/
def xi_time_part9y_window6_visible_odd_tensor_extremal_selector_statement : Prop :=
  xi_time_part9y_window6_visible_odd_tensor_extremal_selector_shell2.length = 5 ∧
    xi_time_part9y_window6_visible_odd_tensor_extremal_selector_shell3.length = 4 ∧
    xi_time_part9y_window6_visible_odd_tensor_extremal_selector_shell4.length = 9 ∧
    xi_time_part9y_window6_visible_odd_tensor_extremal_selector_roots.length = 18 ∧
    (∀ f : ℤ → ℤ,
      xi_time_part9y_window6_visible_odd_tensor_extremal_selector_one_fold_sum f =
        fun i =>
          (f 4 - f 2) *
            xi_time_part9y_window6_visible_odd_tensor_extremal_selector_axis i) ∧
    (∀ f : ℤ → ℤ, ∀ i j k : Fin 3,
      xi_time_part9y_window6_visible_odd_tensor_extremal_selector_cubic_tensor_sum f i j k =
        (f 4 - f 2) *
          xi_time_part9y_window6_visible_odd_tensor_extremal_selector_axis i *
          xi_time_part9y_window6_visible_odd_tensor_extremal_selector_axis j *
          xi_time_part9y_window6_visible_odd_tensor_extremal_selector_axis k)

/-- Paper label: `thm:xi-time-part9y-window6-visible-odd-tensor-extremal-selector`. -/
theorem paper_xi_time_part9y_window6_visible_odd_tensor_extremal_selector :
    xi_time_part9y_window6_visible_odd_tensor_extremal_selector_statement := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · intro f
    funext i
    fin_cases i
    all_goals
      simp [xi_time_part9y_window6_visible_odd_tensor_extremal_selector_one_fold_sum,
        xi_time_part9y_window6_visible_odd_tensor_extremal_selector_shell2,
        xi_time_part9y_window6_visible_odd_tensor_extremal_selector_shell3,
        xi_time_part9y_window6_visible_odd_tensor_extremal_selector_shell4,
        xi_time_part9y_window6_visible_odd_tensor_extremal_selector_vec,
        xi_time_part9y_window6_visible_odd_tensor_extremal_selector_axis] <;>
      ring
  · intro f i j k
    fin_cases i <;> fin_cases j <;> fin_cases k
    all_goals
      simp [xi_time_part9y_window6_visible_odd_tensor_extremal_selector_cubic_tensor_sum,
        xi_time_part9y_window6_visible_odd_tensor_extremal_selector_shell2,
        xi_time_part9y_window6_visible_odd_tensor_extremal_selector_shell3,
        xi_time_part9y_window6_visible_odd_tensor_extremal_selector_shell4,
        xi_time_part9y_window6_visible_odd_tensor_extremal_selector_vec,
        xi_time_part9y_window6_visible_odd_tensor_extremal_selector_axis] <;>
      ring

end Omega.Zeta
