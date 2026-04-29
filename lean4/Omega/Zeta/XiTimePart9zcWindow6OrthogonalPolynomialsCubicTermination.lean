import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

namespace Omega.Zeta

/-- The three-atom window-6 weighted moment functional. -/
def xi_time_part9zc_window6_orthogonal_polynomials_cubic_termination_moment
    (f : ℚ → ℚ) : ℚ :=
  (1 / 4 : ℚ) * f 2 + (3 / 16 : ℚ) * f 3 + (9 / 16 : ℚ) * f 4

/-- Inner product induced by the three-atom window-6 measure. -/
def xi_time_part9zc_window6_orthogonal_polynomials_cubic_termination_inner
    (f g : ℚ → ℚ) : ℚ :=
  xi_time_part9zc_window6_orthogonal_polynomials_cubic_termination_moment
    (fun x => f x * g x)

/-- The constant monic orthogonal polynomial. -/
def xi_time_part9zc_window6_orthogonal_polynomials_cubic_termination_P0
    (_x : ℚ) : ℚ :=
  1

/-- The first monic orthogonal polynomial. -/
def xi_time_part9zc_window6_orthogonal_polynomials_cubic_termination_P1
    (x : ℚ) : ℚ :=
  x - 53 / 16

/-- The second monic orthogonal polynomial. -/
def xi_time_part9zc_window6_orthogonal_polynomials_cubic_termination_P2
    (x : ℚ) : ℚ :=
  x ^ 2 - (371 / 61) * x + 516 / 61

/-- The cubic terminating polynomial on the support. -/
def xi_time_part9zc_window6_orthogonal_polynomials_cubic_termination_P3
    (x : ℚ) : ℚ :=
  (x - 2) * (x - 3) * (x - 4)

/-- The lower quadratic root of `P₂`. -/
noncomputable def xi_time_part9zc_window6_orthogonal_polynomials_cubic_termination_xMinus :
    ℝ :=
  (371 - 11 * Real.sqrt 97) / 122

/-- The upper quadratic root of `P₂`. -/
noncomputable def xi_time_part9zc_window6_orthogonal_polynomials_cubic_termination_xPlus :
    ℝ :=
  (371 + 11 * Real.sqrt 97) / 122

/-- Finite rational arithmetic checks for the window-6 orthogonal polynomial table. -/
def xi_time_part9zc_window6_orthogonal_polynomials_cubic_termination_rationalChecks :
    Prop :=
  xi_time_part9zc_window6_orthogonal_polynomials_cubic_termination_inner
      xi_time_part9zc_window6_orthogonal_polynomials_cubic_termination_P0
      xi_time_part9zc_window6_orthogonal_polynomials_cubic_termination_P0 = 1 ∧
    xi_time_part9zc_window6_orthogonal_polynomials_cubic_termination_inner
      xi_time_part9zc_window6_orthogonal_polynomials_cubic_termination_P1
      xi_time_part9zc_window6_orthogonal_polynomials_cubic_termination_P0 = 0 ∧
    xi_time_part9zc_window6_orthogonal_polynomials_cubic_termination_inner
      xi_time_part9zc_window6_orthogonal_polynomials_cubic_termination_P2
      xi_time_part9zc_window6_orthogonal_polynomials_cubic_termination_P0 = 0 ∧
    xi_time_part9zc_window6_orthogonal_polynomials_cubic_termination_inner
      xi_time_part9zc_window6_orthogonal_polynomials_cubic_termination_P2
      xi_time_part9zc_window6_orthogonal_polynomials_cubic_termination_P1 = 0 ∧
    xi_time_part9zc_window6_orthogonal_polynomials_cubic_termination_inner
      xi_time_part9zc_window6_orthogonal_polynomials_cubic_termination_P3
      xi_time_part9zc_window6_orthogonal_polynomials_cubic_termination_P0 = 0 ∧
    xi_time_part9zc_window6_orthogonal_polynomials_cubic_termination_inner
      xi_time_part9zc_window6_orthogonal_polynomials_cubic_termination_P3
      xi_time_part9zc_window6_orthogonal_polynomials_cubic_termination_P1 = 0 ∧
    xi_time_part9zc_window6_orthogonal_polynomials_cubic_termination_inner
      xi_time_part9zc_window6_orthogonal_polynomials_cubic_termination_P3
      xi_time_part9zc_window6_orthogonal_polynomials_cubic_termination_P2 = 0 ∧
    xi_time_part9zc_window6_orthogonal_polynomials_cubic_termination_inner
      xi_time_part9zc_window6_orthogonal_polynomials_cubic_termination_P1
      xi_time_part9zc_window6_orthogonal_polynomials_cubic_termination_P1 =
        183 / 256 ∧
    xi_time_part9zc_window6_orthogonal_polynomials_cubic_termination_inner
      xi_time_part9zc_window6_orthogonal_polynomials_cubic_termination_P2
      xi_time_part9zc_window6_orthogonal_polynomials_cubic_termination_P2 =
        9 / 61 ∧
    xi_time_part9zc_window6_orthogonal_polynomials_cubic_termination_inner
      xi_time_part9zc_window6_orthogonal_polynomials_cubic_termination_P3
      xi_time_part9zc_window6_orthogonal_polynomials_cubic_termination_P3 = 0

/-- The two quadratic roots interlace strictly with the support points `2, 3, 4`. -/
def xi_time_part9zc_window6_orthogonal_polynomials_cubic_termination_rootInterlacing :
    Prop :=
  (2 : ℝ) <
      xi_time_part9zc_window6_orthogonal_polynomials_cubic_termination_xMinus ∧
    xi_time_part9zc_window6_orthogonal_polynomials_cubic_termination_xMinus < 3 ∧
    (3 : ℝ) <
      xi_time_part9zc_window6_orthogonal_polynomials_cubic_termination_xPlus ∧
    xi_time_part9zc_window6_orthogonal_polynomials_cubic_termination_xPlus < 4

/-- Concrete statement for
`thm:xi-time-part9zc-window6-orthogonal-polynomials-cubic-termination`. -/
def xi_time_part9zc_window6_orthogonal_polynomials_cubic_termination_statement :
    Prop :=
  xi_time_part9zc_window6_orthogonal_polynomials_cubic_termination_rationalChecks ∧
    xi_time_part9zc_window6_orthogonal_polynomials_cubic_termination_rootInterlacing

/-- Paper label:
`thm:xi-time-part9zc-window6-orthogonal-polynomials-cubic-termination`. -/
theorem paper_xi_time_part9zc_window6_orthogonal_polynomials_cubic_termination :
    xi_time_part9zc_window6_orthogonal_polynomials_cubic_termination_statement := by
  refine ⟨?_, ?_⟩
  · norm_num
      [xi_time_part9zc_window6_orthogonal_polynomials_cubic_termination_rationalChecks,
        xi_time_part9zc_window6_orthogonal_polynomials_cubic_termination_inner,
        xi_time_part9zc_window6_orthogonal_polynomials_cubic_termination_moment,
        xi_time_part9zc_window6_orthogonal_polynomials_cubic_termination_P0,
        xi_time_part9zc_window6_orthogonal_polynomials_cubic_termination_P1,
        xi_time_part9zc_window6_orthogonal_polynomials_cubic_termination_P2,
        xi_time_part9zc_window6_orthogonal_polynomials_cubic_termination_P3]
  · have hsqrt_gt9 : (9 : ℝ) < Real.sqrt 97 := by
      rw [Real.lt_sqrt (by norm_num)]
      norm_num
    have hsqrt_lt10 : Real.sqrt 97 < (10 : ℝ) := by
      rw [Real.sqrt_lt (by norm_num) (by norm_num)]
      norm_num
    have hsqrt_nonneg : 0 ≤ Real.sqrt (97 : ℝ) := Real.sqrt_nonneg 97
    unfold xi_time_part9zc_window6_orthogonal_polynomials_cubic_termination_rootInterlacing
    unfold xi_time_part9zc_window6_orthogonal_polynomials_cubic_termination_xMinus
    unfold xi_time_part9zc_window6_orthogonal_polynomials_cubic_termination_xPlus
    constructor
    · nlinarith
    constructor
    · nlinarith
    constructor
    · nlinarith
    · nlinarith

end Omega.Zeta
