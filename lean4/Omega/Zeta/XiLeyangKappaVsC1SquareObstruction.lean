import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete algebraic--transcendental obstruction package for the Lee--Yang `κ` and `c₁²`
coupling.  Algebraic scalars are represented by rational coefficients, while the required
transcendence input is the absence of any rational value for the logarithmic square term. -/
structure xi_leyang_kappa_vs_c1_square_obstruction_data where
  kappa : ℚ
  kappa_ne_zero : kappa ≠ 0
  c1Square : ℝ
  c1Square_ne_zero : c1Square ≠ 0
  logTwoOverPhi : ℝ
  c1Square_eq_logTwoOverPhi : c1Square = logTwoOverPhi
  logTwoOverPhi_not_rational : ∀ q : ℚ, (q : ℝ) ≠ logTwoOverPhi

namespace xi_leyang_kappa_vs_c1_square_obstruction_data

/-- No nonzero rational, hence algebraic in this one-dimensional rational package, can multiply
`c₁²` to produce the algebraic constant `κ`. -/
def noAlgebraicSquareCoupling (D : xi_leyang_kappa_vs_c1_square_obstruction_data) : Prop :=
  ∀ a : ℚ, a ≠ 0 → (a : ℝ) * D.c1Square ≠ (D.kappa : ℝ)

/-- The quotient `κ / c₁²` is not rational in the same package. -/
def ratioTranscendental (D : xi_leyang_kappa_vs_c1_square_obstruction_data) : Prop :=
  ∀ q : ℚ, (q : ℝ) ≠ (D.kappa : ℝ) / D.c1Square

end xi_leyang_kappa_vs_c1_square_obstruction_data

/-- Paper label: `thm:xi-leyang-kappa-vs-c1-square-obstruction`.

A rational nonzero multiple of the irrational logarithmic square term cannot be the rational
constant `κ`; likewise, a rational value of `κ / c₁²` would solve for `c₁²` as rational. -/
theorem paper_xi_leyang_kappa_vs_c1_square_obstruction
    (D : xi_leyang_kappa_vs_c1_square_obstruction_data) :
    D.noAlgebraicSquareCoupling ∧ D.ratioTranscendental := by
  have hno : D.noAlgebraicSquareCoupling := by
    intro a ha hcoupling
    have haR : (a : ℝ) ≠ 0 := by exact_mod_cast ha
    have hsolve : D.c1Square = (D.kappa : ℝ) / (a : ℝ) := by
      rw [← hcoupling]
      field_simp [haR]
    have hcast : (((D.kappa / a : ℚ) : ℝ)) = (D.kappa : ℝ) / (a : ℝ) := by
      norm_num
    exact D.logTwoOverPhi_not_rational (D.kappa / a) (by
      rw [← D.c1Square_eq_logTwoOverPhi, hsolve, ← hcast])
  refine ⟨hno, ?_⟩
  intro q hratio
  by_cases hq : q = 0
  · subst q
    have hkR : (D.kappa : ℝ) ≠ 0 := by exact_mod_cast D.kappa_ne_zero
    have hdiv : (D.kappa : ℝ) / D.c1Square = 0 := by
      simpa using hratio.symm
    rcases div_eq_zero_iff.mp hdiv with hk | hc
    · exact hkR hk
    · exact D.c1Square_ne_zero hc
  · have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq
    have hcoupling : (q : ℝ) * D.c1Square = (D.kappa : ℝ) := by
      have hmul := congrArg (fun x : ℝ => x * D.c1Square) hratio
      field_simp [D.c1Square_ne_zero] at hmul
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
    exact hno q hq hcoupling

end Omega.Zeta
