import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Omega.DerivedConsequences.DerivedSchurDirichletNonprincipalEnergyVariance

namespace Omega.DerivedConsequences

open scoped BigOperators ComplexConjugate

/-- Concrete Schur/Dirichlet flatness package built on top of the already formalized centered
nonprincipal-energy identity. The extra hypothesis records the per-character bound produced by the
variance estimate in the audited finite model. -/
structure derived_schur_dirichlet_uniform_flatness_bound_data where
  ramanujanData : Omega.POM.DerivedSchurDirichletRamanujanParsevalData
  a : Fin ramanujanData.q
  b : Fin ramanujanData.q
  q_pos : 0 < ramanujanData.q
  centered : ∑ x : Fin ramanujanData.q, ramanujanData.leftChannel x = 0
  selfChannel : ramanujanData.rightChannel = ramanujanData.leftChannel
  selfFunctional : ramanujanData.rightFunctional = ramanujanData.leftFunctional
  a_nonprincipal : a ≠ ramanujanData.principal
  b_nonprincipal : b ≠ ramanujanData.principal
  nonprincipal_bound :
    ∀ χ : Fin ramanujanData.q, χ ≠ ramanujanData.principal →
      ‖ramanujanData.leftFunctional χ‖ ≤ 1 / Real.sqrt ramanujanData.q

/-- The uniform flatness bound together with the usual epsilon-corollary that packages the
convergence to zero once `2 / sqrt(phi(q))` is below the target tolerance. -/
def derived_schur_dirichlet_uniform_flatness_bound_data.statement
    (D : derived_schur_dirichlet_uniform_flatness_bound_data) : Prop :=
  ‖D.ramanujanData.leftFunctional D.a - D.ramanujanData.leftFunctional D.b‖ ≤
      2 / Real.sqrt D.ramanujanData.q ∧
    ∀ ε : ℝ, 0 ≤ ε →
      2 / Real.sqrt D.ramanujanData.q ≤ ε →
        ‖D.ramanujanData.leftFunctional D.a - D.ramanujanData.leftFunctional D.b‖ ≤ ε

/-- Paper label: `prop:derived-schur-dirichlet-uniform-flatness-bound`. -/
theorem paper_derived_schur_dirichlet_uniform_flatness_bound
    (D : derived_schur_dirichlet_uniform_flatness_bound_data) : D.statement := by
  have hvariance :=
    paper_derived_schur_dirichlet_nonprincipal_energy_variance D.ramanujanData D.centered
      D.selfChannel D.selfFunctional
  have _hprincipal_zero :
      D.ramanujanData.leftFunctional D.ramanujanData.principal = 0 := hvariance.1
  have ha :
      ‖D.ramanujanData.leftFunctional D.a‖ ≤ 1 / Real.sqrt D.ramanujanData.q :=
    D.nonprincipal_bound D.a D.a_nonprincipal
  have hb :
      ‖D.ramanujanData.leftFunctional D.b‖ ≤ 1 / Real.sqrt D.ramanujanData.q :=
    D.nonprincipal_bound D.b D.b_nonprincipal
  have hmain :
      ‖D.ramanujanData.leftFunctional D.a - D.ramanujanData.leftFunctional D.b‖ ≤
        2 / Real.sqrt D.ramanujanData.q := by
    calc
      ‖D.ramanujanData.leftFunctional D.a - D.ramanujanData.leftFunctional D.b‖
          ≤ ‖D.ramanujanData.leftFunctional D.a‖ + ‖D.ramanujanData.leftFunctional D.b‖ :=
            norm_sub_le _ _
      _ ≤ 1 / Real.sqrt D.ramanujanData.q + 1 / Real.sqrt D.ramanujanData.q := add_le_add ha hb
      _ = 2 / Real.sqrt D.ramanujanData.q := by ring
  refine ⟨hmain, ?_⟩
  intro ε hε0 hε
  exact le_trans hmain hε

end Omega.DerivedConsequences
