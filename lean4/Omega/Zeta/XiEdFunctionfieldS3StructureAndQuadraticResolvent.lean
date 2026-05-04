import Mathlib.Tactic

namespace Omega.Zeta

/-- The Lee--Yang cubic factor in the discriminant of `F(m,y)` over `ℚ(y)`. -/
def xi_ed_functionfield_s3_structure_and_quadratic_resolvent_g (y : ℤ) : ℤ :=
  256 * y ^ 3 + 411 * y ^ 2 + 165 * y + 32

/-- The square-class representative `Δ(y)=-y(y-1)g(y)`. -/
def xi_ed_functionfield_s3_structure_and_quadratic_resolvent_delta (y : ℤ) : ℤ :=
  -y * (y - 1) * xi_ed_functionfield_s3_structure_and_quadratic_resolvent_g y

/-- The discriminant of `F(m,y)` when it is viewed as a cubic in `m`. -/
def xi_ed_functionfield_s3_structure_and_quadratic_resolvent_cubicDiscriminant
    (y : ℤ) : ℤ :=
  -y ^ 3 * (y - 1) * xi_ed_functionfield_s3_structure_and_quadratic_resolvent_g y

/-- The specialization at `y=2` used as the irreducible cubic certificate. -/
def xi_ed_functionfield_s3_structure_and_quadratic_resolvent_specializedCubic
    (m : ℚ) : ℚ :=
  4 * m ^ 3 + 16 * m ^ 2 - 12 * m - 73

/-- Rational-root candidates for `4m^3+16m^2-12m-73`, evaluated away from zero. -/
def xi_ed_functionfield_s3_structure_and_quadratic_resolvent_rationalRootAudit : Prop :=
  xi_ed_functionfield_s3_structure_and_quadratic_resolvent_specializedCubic (1 : ℚ) ≠ 0 ∧
    xi_ed_functionfield_s3_structure_and_quadratic_resolvent_specializedCubic (-1 : ℚ) ≠ 0 ∧
    xi_ed_functionfield_s3_structure_and_quadratic_resolvent_specializedCubic ((1 : ℚ) / 2) ≠ 0 ∧
    xi_ed_functionfield_s3_structure_and_quadratic_resolvent_specializedCubic
        (-(1 : ℚ) / 2) ≠ 0 ∧
    xi_ed_functionfield_s3_structure_and_quadratic_resolvent_specializedCubic ((1 : ℚ) / 4) ≠ 0 ∧
    xi_ed_functionfield_s3_structure_and_quadratic_resolvent_specializedCubic
        (-(1 : ℚ) / 4) ≠ 0 ∧
    xi_ed_functionfield_s3_structure_and_quadratic_resolvent_specializedCubic (73 : ℚ) ≠ 0 ∧
    xi_ed_functionfield_s3_structure_and_quadratic_resolvent_specializedCubic (-73 : ℚ) ≠ 0 ∧
    xi_ed_functionfield_s3_structure_and_quadratic_resolvent_specializedCubic
        ((73 : ℚ) / 2) ≠ 0 ∧
    xi_ed_functionfield_s3_structure_and_quadratic_resolvent_specializedCubic
        (-(73 : ℚ) / 2) ≠ 0 ∧
    xi_ed_functionfield_s3_structure_and_quadratic_resolvent_specializedCubic
        ((73 : ℚ) / 4) ≠ 0 ∧
    xi_ed_functionfield_s3_structure_and_quadratic_resolvent_specializedCubic
        (-(73 : ℚ) / 4) ≠ 0

/-- The two alternatives for an irreducible cubic Galois closure. -/
inductive xi_ed_functionfield_s3_structure_and_quadratic_resolvent_cubicClosureType where
  | cyclicA3
  | fullS3
  deriving DecidableEq

/-- The cubic closure alternative selected by the discriminant squareclass. -/
def xi_ed_functionfield_s3_structure_and_quadratic_resolvent_closureTypeFromSquareclass
    (squareDiscriminant : Bool) :
    xi_ed_functionfield_s3_structure_and_quadratic_resolvent_cubicClosureType :=
  if squareDiscriminant then
    xi_ed_functionfield_s3_structure_and_quadratic_resolvent_cubicClosureType.cyclicA3
  else
    xi_ed_functionfield_s3_structure_and_quadratic_resolvent_cubicClosureType.fullS3

/-- Concrete separability certificate: the cubic discriminant has nonzero specialization. -/
def xi_ed_functionfield_s3_structure_and_quadratic_resolvent_cubicSeparable : Prop :=
  xi_ed_functionfield_s3_structure_and_quadratic_resolvent_cubicDiscriminant 2 ≠ 0

/-- Concrete `S₃` audit from the rational-root table and the nonsquare discriminant squareclass. -/
def xi_ed_functionfield_s3_structure_and_quadratic_resolvent_galoisClosureS3 : Prop :=
  xi_ed_functionfield_s3_structure_and_quadratic_resolvent_rationalRootAudit ∧
    ¬ IsSquare (xi_ed_functionfield_s3_structure_and_quadratic_resolvent_cubicDiscriminant 2) ∧
      xi_ed_functionfield_s3_structure_and_quadratic_resolvent_closureTypeFromSquareclass false =
        xi_ed_functionfield_s3_structure_and_quadratic_resolvent_cubicClosureType.fullS3

/-- Concrete quadratic-resolvent certificate `Disc_m(F)=y²Δ(y)`. -/
def xi_ed_functionfield_s3_structure_and_quadratic_resolvent_quadraticResolventByDelta :
    Prop :=
  (∀ y : ℤ,
    xi_ed_functionfield_s3_structure_and_quadratic_resolvent_cubicDiscriminant y =
      y ^ 2 * xi_ed_functionfield_s3_structure_and_quadratic_resolvent_delta y) ∧
    xi_ed_functionfield_s3_structure_and_quadratic_resolvent_delta 2 = -8108

private theorem xi_ed_functionfield_s3_structure_and_quadratic_resolvent_rootAudit_true :
    xi_ed_functionfield_s3_structure_and_quadratic_resolvent_rationalRootAudit := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [xi_ed_functionfield_s3_structure_and_quadratic_resolvent_specializedCubic]

private theorem xi_ed_functionfield_s3_structure_and_quadratic_resolvent_disc_two :
    xi_ed_functionfield_s3_structure_and_quadratic_resolvent_cubicDiscriminant 2 = -32432 := by
  norm_num [xi_ed_functionfield_s3_structure_and_quadratic_resolvent_cubicDiscriminant,
    xi_ed_functionfield_s3_structure_and_quadratic_resolvent_g]

private theorem xi_ed_functionfield_s3_structure_and_quadratic_resolvent_disc_two_not_square :
    ¬ IsSquare (xi_ed_functionfield_s3_structure_and_quadratic_resolvent_cubicDiscriminant 2) := by
  intro hsq
  rcases hsq with ⟨n, hn⟩
  have hnonneg : 0 ≤ xi_ed_functionfield_s3_structure_and_quadratic_resolvent_cubicDiscriminant 2 := by
    simpa [pow_two, hn] using sq_nonneg n
  rw [xi_ed_functionfield_s3_structure_and_quadratic_resolvent_disc_two] at hnonneg
  norm_num at hnonneg

/-- Paper label: `cor:xi-ed-functionfield-s3-structure-and-quadratic-resolvent`. -/
theorem paper_xi_ed_functionfield_s3_structure_and_quadratic_resolvent :
    xi_ed_functionfield_s3_structure_and_quadratic_resolvent_cubicSeparable ∧
      xi_ed_functionfield_s3_structure_and_quadratic_resolvent_galoisClosureS3 ∧
        xi_ed_functionfield_s3_structure_and_quadratic_resolvent_quadraticResolventByDelta := by
  refine ⟨?_, ?_, ?_⟩
  · unfold xi_ed_functionfield_s3_structure_and_quadratic_resolvent_cubicSeparable
    rw [xi_ed_functionfield_s3_structure_and_quadratic_resolvent_disc_two]
    norm_num
  · refine ⟨xi_ed_functionfield_s3_structure_and_quadratic_resolvent_rootAudit_true,
      xi_ed_functionfield_s3_structure_and_quadratic_resolvent_disc_two_not_square, ?_⟩
    rfl
  · refine ⟨?_, ?_⟩
    · intro y
      simp [xi_ed_functionfield_s3_structure_and_quadratic_resolvent_cubicDiscriminant,
        xi_ed_functionfield_s3_structure_and_quadratic_resolvent_delta]
      ring
    · norm_num [xi_ed_functionfield_s3_structure_and_quadratic_resolvent_delta,
        xi_ed_functionfield_s3_structure_and_quadratic_resolvent_g]

end Omega.Zeta
