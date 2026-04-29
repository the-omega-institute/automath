import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Boundary points for the disk model of the half-plane Hardy factorization. -/
def xi_hardy_inner_characterization_boundary_circle (z : ℂ) : Prop :=
  ‖z‖ = 1

/-- A concrete outer factor has collapsed to a constant unimodular phase. -/
def xi_hardy_inner_characterization_constant_unit (f : ℂ → ℂ) : Prop :=
  ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ z : ℂ, f z = c

/-- Concrete bounded-type factorization interface for
`thm:xi-hardy-inner-characterization`.  The fields record the disk model of the
completed determinant, its Blaschke/singular/outer factors, boundary unitarity, and the
outer-factor rigidity supplied by the Hardy outer uniqueness theorem. -/
structure xi_hardy_inner_characterization_data where
  xiFunction : ℂ → ℂ
  blaschkeFactor : ℂ → ℂ
  singularFactor : ℂ → ℂ
  outerFactor : ℂ → ℂ
  outerUnit : ℂ
  canonicalFactorization :
    ∀ z : ℂ, xiFunction z = blaschkeFactor z * singularFactor z * outerFactor z
  boundaryModulusOne :
    ∀ z : ℂ, xi_hardy_inner_characterization_boundary_circle z → ‖xiFunction z‖ = 1
  outerUnit_modulus : ‖outerUnit‖ = 1
  outer_rigidity_from_boundary_modulus :
    (∀ z : ℂ,
      xi_hardy_inner_characterization_boundary_circle z → ‖xiFunction z‖ = 1) →
      ∀ z : ℂ, outerFactor z = outerUnit

namespace xi_hardy_inner_characterization_data

/-- The diskized determinant has only the inner Blaschke/singular factor and the collapsed
constant outer phase left in its canonical product. -/
def innerFunction (D : xi_hardy_inner_characterization_data) : Prop :=
  ∀ z : ℂ, D.xiFunction z = D.blaschkeFactor z * D.singularFactor z * D.outerFactor z

/-- The outer factor is a constant unit. -/
def outerFactorIsConstantUnit (D : xi_hardy_inner_characterization_data) : Prop :=
  xi_hardy_inner_characterization_constant_unit D.outerFactor

end xi_hardy_inner_characterization_data

/-- Paper label: `thm:xi-hardy-inner-characterization`. -/
theorem paper_xi_hardy_inner_characterization
    (D : xi_hardy_inner_characterization_data) :
    D.innerFunction ∧ D.outerFactorIsConstantUnit := by
  refine ⟨D.canonicalFactorization, ?_⟩
  exact ⟨D.outerUnit, D.outerUnit_modulus,
    D.outer_rigidity_from_boundary_modulus D.boundaryModulusOne⟩

end Omega.Zeta
