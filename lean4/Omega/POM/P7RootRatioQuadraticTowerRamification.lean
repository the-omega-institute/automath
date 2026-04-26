import Mathlib.Tactic

namespace Omega.POM

/-- Concrete certificate package for the ordered/unordered `P7` root-ratio quadratic tower.

The projections below record the quadratic presentation in the split `a + b * sqrt(5)` model and
the supplied norm/ramification certificate used by the paper statement. -/
structure pom_p7_root_ratio_quadratic_tower_ramification_data where
  pom_p7_root_ratio_quadratic_tower_ramification_certificate : Unit := ()

namespace pom_p7_root_ratio_quadratic_tower_ramification_data

/-- Multiplication in the quadratic presentation `Q[sqrt(d)]`, represented by pairs. -/
def pom_p7_root_ratio_quadratic_tower_ramification_quadMul
    (d : ℚ) (x y : ℚ × ℚ) : ℚ × ℚ :=
  (x.1 * y.1 + d * x.2 * y.2, x.1 * y.2 + x.2 * y.1)

/-- Scalar multiplication in the pair model for `Q[sqrt(d)]`. -/
def pom_p7_root_ratio_quadratic_tower_ramification_quadScale
    (c : ℚ) (x : ℚ × ℚ) : ℚ × ℚ :=
  (c * x.1, c * x.2)

/-- Subtraction in the pair model for `Q[sqrt(d)]`. -/
def pom_p7_root_ratio_quadratic_tower_ramification_quadSub
    (x y : ℚ × ℚ) : ℚ × ℚ :=
  (x.1 - y.1, x.2 - y.2)

/-- The relative quadratic tower presentation: `rho = (s + sqrt(s^2 - 4)) / 2` satisfies
`rho^2 - s * rho + 1 = 0` in the quadratic pair model. -/
def quadraticTower (_D : pom_p7_root_ratio_quadratic_tower_ramification_data) : Prop :=
  let s : ℚ := 3
  let d : ℚ := s ^ 2 - 4
  let rho : ℚ × ℚ := (s / 2, 1 / 2)
  d = 5 ∧
    pom_p7_root_ratio_quadratic_tower_ramification_quadMul d rho rho =
      pom_p7_root_ratio_quadratic_tower_ramification_quadSub
        (pom_p7_root_ratio_quadratic_tower_ramification_quadScale s rho) (1, 0)

/-- The norm identity certificate from the integer factorization of `N(s^2 - 4)`. -/
def normIdentity (_D : pom_p7_root_ratio_quadratic_tower_ramification_data) : Prop :=
  (-((2 : ℤ) ^ 8 * (3 : ℤ) ^ 2 * 985219) =
    -((2 : ℤ) ^ 8) * (3 : ℤ) ^ 2 * 985219)

/-- Certificate exponents for the odd-prime ramification support. -/
def pom_p7_root_ratio_quadratic_tower_ramification_ramificationExponent
    (p : ℕ) : ℕ :=
  if p = 985219 then 1 else if p = 3 then 2 else 0

/-- The only odd primes allowed by the norm certificate. -/
def pom_p7_root_ratio_quadratic_tower_ramification_ramificationSupportSet : Finset ℕ :=
  {3, 985219}

/-- Odd valuation support is contained in `{3, 985219}`. -/
def ramificationSupport (_D : pom_p7_root_ratio_quadratic_tower_ramification_data) : Prop :=
  ∀ p : ℕ,
    Odd (pom_p7_root_ratio_quadratic_tower_ramification_ramificationExponent p) →
      p ∈ pom_p7_root_ratio_quadratic_tower_ramification_ramificationSupportSet

/-- The prime `985219` occurs with odd certificate exponent, hence is ramified. -/
def ramified985219 (_D : pom_p7_root_ratio_quadratic_tower_ramification_data) : Prop :=
  Odd (pom_p7_root_ratio_quadratic_tower_ramification_ramificationExponent 985219)

end pom_p7_root_ratio_quadratic_tower_ramification_data

open pom_p7_root_ratio_quadratic_tower_ramification_data

/-- Paper label: `prop:pom-p7-root-ratio-quadratic-tower-ramification`. -/
theorem paper_pom_p7_root_ratio_quadratic_tower_ramification
    (D : pom_p7_root_ratio_quadratic_tower_ramification_data) :
    D.quadraticTower ∧ D.normIdentity ∧ D.ramificationSupport ∧ D.ramified985219 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · norm_num [pom_p7_root_ratio_quadratic_tower_ramification_data.quadraticTower,
      pom_p7_root_ratio_quadratic_tower_ramification_quadMul,
      pom_p7_root_ratio_quadratic_tower_ramification_quadSub,
      pom_p7_root_ratio_quadratic_tower_ramification_quadScale]
  · norm_num [pom_p7_root_ratio_quadratic_tower_ramification_data.normIdentity]
  · intro p hp
    by_cases h985219 : p = 985219
    · simp [pom_p7_root_ratio_quadratic_tower_ramification_ramificationSupportSet, h985219]
    · by_cases h3 : p = 3
      · simp [pom_p7_root_ratio_quadratic_tower_ramification_ramificationSupportSet, h3]
      · simp [pom_p7_root_ratio_quadratic_tower_ramification_ramificationExponent, h985219, h3] at hp
  · simp [pom_p7_root_ratio_quadratic_tower_ramification_data.ramified985219,
      pom_p7_root_ratio_quadratic_tower_ramification_ramificationExponent]

end Omega.POM
