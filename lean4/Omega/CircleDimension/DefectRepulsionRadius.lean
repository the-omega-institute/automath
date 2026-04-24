import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Omega.TypedAddressBiaxialCompletion.HorizonPurityRepulsion
import Omega.TypedAddressBiaxialCompletion.JensenDefectFiniteization

namespace Omega.CircleDimension

open Omega.TypedAddressBiaxialCompletion

set_option maxHeartbeats 400000 in
/-- Paper-facing repulsion-radius package: the Jensen-defect finiteization supplies the zero-free
semantics on each radius layer, the explicit radius formula gives the quantitative lower bound
`r_*(ρ) ≥ ρ * exp (-ε)` under `D(ρ) ≤ ε`, and a sequence of radii whose repulsion radii are equal
to the original radii and tend to `1` yields the RH-facing horizon-purity conclusion.
    thm:cdim-defect-repulsion-radius -/
theorem paper_cdim_defect_repulsion_radius
    (defect : ℝ → ℝ) (zeroFree : ℝ → Prop)
    (rho : ℕ → ℝ) (eps : ℕ → ℝ)
    (hSem : ∀ {ρ : ℝ}, 0 < ρ → ρ < 1 →
      0 ≤ defect ρ ∧ (defect ρ = 0 ↔ zeroFree ρ))
    (hRhoPos : ∀ n : ℕ, 0 < rho n)
    (hRhoLt : ∀ n : ℕ, rho n < 1)
    (hDefectLe : ∀ n : ℕ, defect (rho n) ≤ eps n)
    (hRepEq : ∀ n : ℕ, repulsionRadius (rho n) (defect (rho n)) = rho n)
    (hTend : radiiTendToOne rho) :
    (∀ n : ℕ, zeroFree (rho n)) ∧
      (∀ n : ℕ, rho n * Real.exp (-eps n) ≤ repulsionRadius (rho n) (defect (rho n))) ∧
      rhHorizonPurity (fun n => defect (rho n)) := by
  let D : JensenDefectFiniteizationData := {
    defect := defect
    zeroFree := zeroFree
    semantics := by
      intro ρ hρ hρlt
      exact hSem hρ hρlt
  }
  have hFinite :
      ∀ {ρ : ℝ}, 0 < ρ → ρ < 1 →
        0 ≤ D.defect ρ ∧ (D.defect ρ = 0 ↔ D.zeroFree ρ) :=
    paper_typed_address_biaxial_completion_jensen_defect_finiteization D
  refine ⟨?_, ?_, ?_⟩
  · intro n
    have hZero : defect (rho n) = 0 :=
      defect_eq_zero_of_repulsion_eq_radius (hRhoPos n) (hRepEq n)
    exact (hFinite (hRhoPos n) (hRhoLt n)).2.mp hZero
  · intro n
    have hExp : Real.exp (-eps n) ≤ Real.exp (-defect (rho n)) := by
      apply Real.exp_le_exp.mpr
      linarith [hDefectLe n]
    have hRhoNonneg : 0 ≤ rho n := le_of_lt (hRhoPos n)
    calc
      rho n * Real.exp (-eps n) ≤ rho n * Real.exp (-defect (rho n)) := by
        exact mul_le_mul_of_nonneg_left hExp hRhoNonneg
      _ = repulsionRadius (rho n) (defect (rho n)) := rfl
  · exact repulsion_radius_tends_to_one_implies_rh (fun n => defect (rho n)) rho hTend
      hRhoPos hRepEq

end Omega.CircleDimension
