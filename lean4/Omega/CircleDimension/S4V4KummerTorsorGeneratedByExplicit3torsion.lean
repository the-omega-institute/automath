import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Omega.CircleDimension.S4V4CompatibleBiellipticPencilsExactlyThree
import Omega.CircleDimension.S4V4ComplementaryBranchSquareRootLineBundle

namespace Omega.CircleDimension

/-- The quadratic radicand of the base field `K = ℚ(√-3)` used in the Kummer description. -/
def cdim_s4_v4_kummer_torsor_generated_by_explicit_3torsion_base_field_radicand : ℤ :=
  -3

/-- The explicit torsion class has order three in the bookkeeping model. -/
def cdim_s4_v4_kummer_torsor_generated_by_explicit_3torsion_eta_order : ℕ :=
  3

/-- The explicit Kummer extension equation. -/
def cdim_s4_v4_kummer_torsor_generated_by_explicit_3torsion_kummer_extension_equation
    (W Θ : ℂ) : Prop :=
  W ^ 3 = Θ

/-- The resulting `C₃`-torsor is the simply transitive action on the three compatible pencils. -/
def cdim_s4_v4_kummer_torsor_generated_by_explicit_3torsion_generated_torsor : Prop :=
  s4v4CompatibleBiellipticC3ActsSimplyTransitively

/-- Paper label: `thm:cdim-s4-v4-kummer-torsor-generated-by-explicit-3torsion`. The complementary
branch divisor provides the degree-three line-bundle class, the three compatible pencils furnish
the `C₃`-torsor, and the Kummer model is the explicit cubic equation `W^3 = Θ` over `ℚ(√-3)`. -/
theorem paper_cdim_s4_v4_kummer_torsor_generated_by_explicit_3torsion
    (infinityFiber : Finset S4V4FiberPoint) (hcard : infinityFiber.card = 3) :
    let D : S4V4ComplementaryRamificationData := ⟨infinityFiber, hcard⟩
    D.complementaryBranchLinearEquiv ∧
      divisorDegree D.pullbackInfinityDivisor = 3 ∧
      s4v4CompatibleBiellipticPencils.card = 3 ∧
      cdim_s4_v4_kummer_torsor_generated_by_explicit_3torsion_eta_order = 3 ∧
      cdim_s4_v4_kummer_torsor_generated_by_explicit_3torsion_generated_torsor ∧
      cdim_s4_v4_kummer_torsor_generated_by_explicit_3torsion_base_field_radicand = -3 ∧
      (∀ W Θ : ℂ,
        cdim_s4_v4_kummer_torsor_generated_by_explicit_3torsion_kummer_extension_equation W Θ ↔
          W ^ 3 = Θ) := by
  let D : S4V4ComplementaryRamificationData := ⟨infinityFiber, hcard⟩
  have hbranch := paper_cdim_s4_v4_complementary_branch_square_root_line_bundle infinityFiber hcard
  have hpencils := paper_cdim_s4_v4_compatible_bielliptic_pencils_exactly_three
  change D.complementaryBranchLinearEquiv ∧
      divisorDegree D.pullbackInfinityDivisor = 3 ∧
      s4v4CompatibleBiellipticPencils.card = 3 ∧
      cdim_s4_v4_kummer_torsor_generated_by_explicit_3torsion_eta_order = 3 ∧
      cdim_s4_v4_kummer_torsor_generated_by_explicit_3torsion_generated_torsor ∧
      cdim_s4_v4_kummer_torsor_generated_by_explicit_3torsion_base_field_radicand = -3 ∧
      (∀ W Θ : ℂ,
        cdim_s4_v4_kummer_torsor_generated_by_explicit_3torsion_kummer_extension_equation W Θ ↔
          W ^ 3 = Θ)
  refine ⟨hbranch.1, hbranch.2, hpencils.1, rfl, hpencils.2, rfl, ?_⟩
  intro W Θ
  rfl

end Omega.CircleDimension
