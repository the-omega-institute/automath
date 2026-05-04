import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Finite-band scale-Mellin coefficients together with the compact support radius of the
weight.  The proof obligations below use only these concrete numeric fields. -/
structure xi_scale_mellin_cartwright_explicit_type_finite_band_package where
  bandwidthJ : ℕ
  bandwidthK : ℕ
  supportRadius : ℕ
  coefficients : Fin (bandwidthJ + 1) → Fin (2 * bandwidthK + 1) → ℂ

/-- The explicit finite-band Cartwright type used by the paper wrapper. -/
def xi_scale_mellin_cartwright_explicit_type_typeBound
    (D : xi_scale_mellin_cartwright_explicit_type_finite_band_package) : ℕ :=
  D.supportRadius * (D.bandwidthJ + 2 * D.bandwidthK + 1)

/-- Compact support is represented by the numeric radius `supportRadius`. -/
def xi_scale_mellin_cartwright_explicit_type_compactSupport
    (D : xi_scale_mellin_cartwright_explicit_type_finite_band_package)
    (support : ℤ → Prop) : Prop :=
  ∀ z : ℤ, support z → z.natAbs ≤ D.supportRadius

/-- The exponential-type estimate is the concrete `XB` bound for the finite-band package. -/
def xi_scale_mellin_cartwright_explicit_type_exponentialTypeBound
    (D : xi_scale_mellin_cartwright_explicit_type_finite_band_package)
    (typeOf : ℕ) : Prop :=
  typeOf ≤ xi_scale_mellin_cartwright_explicit_type_typeBound D

/-- Cartwright zero-density input: a count with type `typeOf` has at most
`2 * typeOf * T` zeros in the height window `T`. -/
def xi_scale_mellin_cartwright_explicit_type_cartwrightDensity
    (zeroCount : ℕ → ℕ) (typeOf : ℕ) : Prop :=
  ∀ T : ℕ, zeroCount T ≤ 2 * typeOf * (T + 1)

/-- The explicit density conclusion after substituting the finite-band type bound. -/
def xi_scale_mellin_cartwright_explicit_type_zeroDensityConclusion
    (D : xi_scale_mellin_cartwright_explicit_type_finite_band_package)
    (zeroCount : ℕ → ℕ) : Prop :=
  ∀ T : ℕ,
    zeroCount T ≤
      2 * xi_scale_mellin_cartwright_explicit_type_typeBound D * (T + 1)

/-- Concrete paper-facing statement for the finite-band compact-support Cartwright estimate. -/
def xi_scale_mellin_cartwright_explicit_type_statement : Prop :=
  ∀ (D : xi_scale_mellin_cartwright_explicit_type_finite_band_package)
    (support : ℤ → Prop) (zeroCount : ℕ → ℕ) (typeOf : ℕ),
    xi_scale_mellin_cartwright_explicit_type_compactSupport D support →
      xi_scale_mellin_cartwright_explicit_type_exponentialTypeBound D typeOf →
        xi_scale_mellin_cartwright_explicit_type_cartwrightDensity zeroCount typeOf →
          xi_scale_mellin_cartwright_explicit_type_zeroDensityConclusion D zeroCount

/-- Paper label: `prop:xi-scale-mellin-cartwright-explicit-type`. -/
theorem paper_xi_scale_mellin_cartwright_explicit_type :
    xi_scale_mellin_cartwright_explicit_type_statement := by
  intro D _support zeroCount typeOf _hSupport hType hCartwright T
  exact le_trans (hCartwright T) (Nat.mul_le_mul_right (T + 1) (Nat.mul_le_mul_left 2 hType))

end Omega.Zeta
