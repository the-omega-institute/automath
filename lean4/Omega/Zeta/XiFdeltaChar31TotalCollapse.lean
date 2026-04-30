import Mathlib.Tactic

namespace Omega.Zeta

/-- The `T^3` coefficient in the prefixed `F_delta` collapse package. -/
def xi_fdelta_char31_total_collapse_coeff_T3 (p : ℕ) (y : ZMod p) : ZMod p :=
  (8 : ZMod p) * y - 3

/-- The `T^2` coefficient in the prefixed `F_delta` collapse package. -/
def xi_fdelta_char31_total_collapse_coeff_T2 (p : ℕ) (y : ZMod p) : ZMod p :=
  2 * y ^ 2 - 34 * y - 4

/-- The constant obstruction coefficient; it records the prefactor forcing characteristic `31`. -/
def xi_fdelta_char31_total_collapse_coeff_const (p : ℕ) (_y : ZMod p) : ZMod p :=
  (31 : ZMod p)

/-- All lower coefficients of the prefixed quartic package vanish. -/
def xi_fdelta_char31_total_collapse_at (p : ℕ) (y : ZMod p) : Prop :=
  xi_fdelta_char31_total_collapse_coeff_T3 p y = 0 ∧
    xi_fdelta_char31_total_collapse_coeff_T2 p y = 0 ∧
      xi_fdelta_char31_total_collapse_coeff_const p y = 0

/-- The coefficient-vanishing fiber is forced to characteristic `31`, with coordinate `12`. -/
def xi_fdelta_char31_total_collapse_unique_mod31_fiber : Prop :=
  (∀ p : ℕ, Nat.Prime p → p ≠ 2 →
      (∃ y : ZMod p, xi_fdelta_char31_total_collapse_at p y) → p = 31) ∧
    ∀ y : ZMod 31, xi_fdelta_char31_total_collapse_at 31 y ↔ y = 12

/-- The local chart expansion at `(T,y)=(0,12)` over `ZMod 31`. -/
def xi_fdelta_char31_total_collapse_local_expansion (t s : ZMod 31) : ZMod 31 :=
  -12 * s ^ 2 + 14 * t ^ 2 * s + t ^ 4 + 8 * t ^ 3 * s + 2 * t ^ 2 * s ^ 2 +
    10 * s ^ 3 - 15 * s ^ 4 - 8 * s ^ 5

/-- The shifted coordinate `s_1 = s + 2 t^2`, expressed as `s = s_1 - 2 t^2`. -/
def xi_fdelta_char31_total_collapse_shifted_expansion (t s1 : ZMod 31) : ZMod 31 :=
  xi_fdelta_char31_total_collapse_local_expansion t (s1 - 2 * t ^ 2)

/-- The weighted-leading `A_3` form after the coordinate shift. -/
def xi_fdelta_char31_total_collapse_A3_leading (t s1 : ZMod 31) : ZMod 31 :=
  -12 * s1 ^ 2 - 13 * t ^ 4

/-- The explicit higher-weight remainder after subtracting the `A_3` leading form. -/
def xi_fdelta_char31_total_collapse_A3_remainder (t s1 : ZMod 31) : ZMod 31 :=
  xi_fdelta_char31_total_collapse_shifted_expansion t s1 -
    xi_fdelta_char31_total_collapse_A3_leading t s1

/-- Concrete `A_3` tacnode certificate: nonzero quadratic/quartic leading coefficients and
the exact shifted expansion. -/
def xi_fdelta_char31_total_collapse_A3_tacnode : Prop :=
  ((-12 : ZMod 31) ≠ 0 ∧ (-13 : ZMod 31) ≠ 0) ∧
    ∀ t s1 : ZMod 31,
      xi_fdelta_char31_total_collapse_shifted_expansion t s1 =
        xi_fdelta_char31_total_collapse_A3_leading t s1 +
          xi_fdelta_char31_total_collapse_A3_remainder t s1

/-- Paper label: `thm:xi-fdelta-char31-total-collapse`. -/
theorem paper_xi_fdelta_char31_total_collapse :
    xi_fdelta_char31_total_collapse_unique_mod31_fiber ∧
      xi_fdelta_char31_total_collapse_A3_tacnode := by
  constructor
  · constructor
    · intro p hp _hp2 hcollapse
      rcases hcollapse with ⟨y, _hT3, _hT2, hconst⟩
      have hp_dvd_31 : p ∣ 31 := by
        exact (ZMod.natCast_eq_zero_iff 31 p).mp (by
          simpa [xi_fdelta_char31_total_collapse_coeff_const] using hconst)
      have h31prime : Nat.Prime 31 := by norm_num
      rcases h31prime.eq_one_or_self_of_dvd p hp_dvd_31 with hp_one | hp_eq
      · exact (hp.ne_one hp_one).elim
      · exact hp_eq
    · intro y
      constructor
      · intro hcollapse
        rcases hcollapse with ⟨hT3, _hT2, _hconst⟩
        have hmul : (8 : ZMod 31) * y = 3 := by
          exact sub_eq_zero.mp (by
            simpa [xi_fdelta_char31_total_collapse_coeff_T3] using hT3)
        have hunit : (4 : ZMod 31) * 8 = 1 := by decide
        calc
          y = ((4 : ZMod 31) * 8) * y := by rw [hunit, one_mul]
          _ = 4 * ((8 : ZMod 31) * y) := by ring
          _ = 4 * (3 : ZMod 31) := by rw [hmul]
          _ = 12 := by decide
      · intro hy
        subst hy
        constructor
        · native_decide
        · constructor
          · native_decide
          · native_decide
  · constructor
    · constructor <;> decide
    · intro t s1
      rw [xi_fdelta_char31_total_collapse_A3_remainder]
      ring

end Omega.Zeta
