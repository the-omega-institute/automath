import Mathlib.Tactic

namespace Omega.Zeta

/--
Concrete certificate package for the `F_delta` first-subresultant audit.  The linear
subresultant is represented by `sresSlope * T + sresConst`; the two gcd-obstruction
factors are represented by their linear coefficients.  The obstruction certificate says
that a higher collision, i.e. a common zero of the subresultant and both obstruction
factors, must be the recorded double root.
-/
structure xi_fdelta_subresultant_unique_double_root_data where
  xi_fdelta_subresultant_unique_double_root_sresSlope : ℚ
  xi_fdelta_subresultant_unique_double_root_sresConst : ℚ
  xi_fdelta_subresultant_unique_double_root_doubleRoot : ℚ
  xi_fdelta_subresultant_unique_double_root_specialRoot : ℚ
  xi_fdelta_subresultant_unique_double_root_leftSlope : ℚ
  xi_fdelta_subresultant_unique_double_root_leftConst : ℚ
  xi_fdelta_subresultant_unique_double_root_rightSlope : ℚ
  xi_fdelta_subresultant_unique_double_root_rightConst : ℚ
  xi_fdelta_subresultant_unique_double_root_subresultant_certificate :
    xi_fdelta_subresultant_unique_double_root_sresSlope *
        xi_fdelta_subresultant_unique_double_root_doubleRoot +
      xi_fdelta_subresultant_unique_double_root_sresConst = 0
  xi_fdelta_subresultant_unique_double_root_sresSlope_ne_zero :
    xi_fdelta_subresultant_unique_double_root_sresSlope ≠ 0
  xi_fdelta_subresultant_unique_double_root_gcd_obstruction_certificate :
    ∀ T : ℚ,
      xi_fdelta_subresultant_unique_double_root_sresSlope * T +
            xi_fdelta_subresultant_unique_double_root_sresConst = 0 →
        xi_fdelta_subresultant_unique_double_root_leftSlope * T +
            xi_fdelta_subresultant_unique_double_root_leftConst = 0 →
          xi_fdelta_subresultant_unique_double_root_rightSlope * T +
              xi_fdelta_subresultant_unique_double_root_rightConst = 0 →
            T = xi_fdelta_subresultant_unique_double_root_doubleRoot
  xi_fdelta_subresultant_unique_double_root_special_root_certificate :
    xi_fdelta_subresultant_unique_double_root_specialRoot = 0

namespace xi_fdelta_subresultant_unique_double_root_data

/-- The certified first subresultant as a linear polynomial in the collision coordinate. -/
def xi_fdelta_subresultant_unique_double_root_sres
    (D : xi_fdelta_subresultant_unique_double_root_data) (T : ℚ) : ℚ :=
  D.xi_fdelta_subresultant_unique_double_root_sresSlope * T +
    D.xi_fdelta_subresultant_unique_double_root_sresConst

/-- First obstruction factor in the certified gcd audit. -/
def xi_fdelta_subresultant_unique_double_root_leftFactor
    (D : xi_fdelta_subresultant_unique_double_root_data) (T : ℚ) : ℚ :=
  D.xi_fdelta_subresultant_unique_double_root_leftSlope * T +
    D.xi_fdelta_subresultant_unique_double_root_leftConst

/-- Second obstruction factor in the certified gcd audit. -/
def xi_fdelta_subresultant_unique_double_root_rightFactor
    (D : xi_fdelta_subresultant_unique_double_root_data) (T : ℚ) : ℚ :=
  D.xi_fdelta_subresultant_unique_double_root_rightSlope * T +
    D.xi_fdelta_subresultant_unique_double_root_rightConst

/-- Closed form: the recorded double root annihilates the linear first subresultant. -/
def subresultant_closed_form (D : xi_fdelta_subresultant_unique_double_root_data) : Prop :=
  D.xi_fdelta_subresultant_unique_double_root_sres
    D.xi_fdelta_subresultant_unique_double_root_doubleRoot = 0

/-- Higher collisions are killed by the certified coprime obstruction factors. -/
def unique_double_root (D : xi_fdelta_subresultant_unique_double_root_data) : Prop :=
  ∀ T : ℚ,
    D.xi_fdelta_subresultant_unique_double_root_sres T = 0 →
      D.xi_fdelta_subresultant_unique_double_root_leftFactor T = 0 →
        D.xi_fdelta_subresultant_unique_double_root_rightFactor T = 0 →
          T = D.xi_fdelta_subresultant_unique_double_root_doubleRoot

/-- Solving the nonzero linear subresultant gives the closed double-root coordinate. -/
def double_root_formula (D : xi_fdelta_subresultant_unique_double_root_data) : Prop :=
  D.xi_fdelta_subresultant_unique_double_root_doubleRoot =
    -D.xi_fdelta_subresultant_unique_double_root_sresConst /
      D.xi_fdelta_subresultant_unique_double_root_sresSlope

/-- The distinguished special root in the audit is the origin. -/
def special_root_zero (D : xi_fdelta_subresultant_unique_double_root_data) : Prop :=
  D.xi_fdelta_subresultant_unique_double_root_specialRoot = 0

end xi_fdelta_subresultant_unique_double_root_data

/-- Paper label: `thm:xi-fdelta-subresultant-unique-double-root`. -/
theorem paper_xi_fdelta_subresultant_unique_double_root
    (D : xi_fdelta_subresultant_unique_double_root_data) :
    D.subresultant_closed_form ∧ D.unique_double_root ∧ D.double_root_formula ∧
      D.special_root_zero := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [xi_fdelta_subresultant_unique_double_root_data.subresultant_closed_form,
      xi_fdelta_subresultant_unique_double_root_data.xi_fdelta_subresultant_unique_double_root_sres]
      using D.xi_fdelta_subresultant_unique_double_root_subresultant_certificate
  · intro T hS hL hR
    exact D.xi_fdelta_subresultant_unique_double_root_gcd_obstruction_certificate T hS hL hR
  · unfold xi_fdelta_subresultant_unique_double_root_data.double_root_formula
    have hmul :
        D.xi_fdelta_subresultant_unique_double_root_sresSlope *
            D.xi_fdelta_subresultant_unique_double_root_doubleRoot =
          -D.xi_fdelta_subresultant_unique_double_root_sresConst := by
      linarith [D.xi_fdelta_subresultant_unique_double_root_subresultant_certificate]
    calc
      D.xi_fdelta_subresultant_unique_double_root_doubleRoot =
          (D.xi_fdelta_subresultant_unique_double_root_sresSlope *
              D.xi_fdelta_subresultant_unique_double_root_doubleRoot) /
            D.xi_fdelta_subresultant_unique_double_root_sresSlope := by
            field_simp [D.xi_fdelta_subresultant_unique_double_root_sresSlope_ne_zero]
      _ = -D.xi_fdelta_subresultant_unique_double_root_sresConst /
            D.xi_fdelta_subresultant_unique_double_root_sresSlope := by
            rw [hmul]
  · exact D.xi_fdelta_subresultant_unique_double_root_special_root_certificate

end Omega.Zeta
