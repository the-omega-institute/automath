import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
import Omega.SPG.GraphCycleLatticeWeightedDiscriminant

namespace Omega.SPG

open scoped BigOperators

/-- Concrete finite package for the phase form of the weighted cycle-lattice discriminant:
the nonzero Laplacian modes are indexed by a finite type, each eigenvalue is written in the
Lee--Yang phase form `4 D sin²(θ/2)`, and the tree polynomial is identified with the product of
the nonzero modes divided by `|V|`. -/
structure GraphCycleLatticeLeyangPhasePackage where
  weighted : GraphCycleLatticeWeightedDiscriminantData
  Mode : Type
  instFintypeMode : Fintype Mode
  theta : Mode → ℝ
  phaseScale : ℝ
  vertexCount : ℕ
  vertexCount_ne_zero : vertexCount ≠ 0
  laplacianEigenvalue : Mode → ℝ
  treePolynomial_eq :
    GraphCycleLatticeWeightedDiscriminantData.reciprocalTreePolynomial weighted =
      ((vertexCount : ℝ)⁻¹) * ∏ j : Mode, laplacianEigenvalue j
  phaseCompat :
    ∀ j : Mode,
      laplacianEigenvalue j = (4 * phaseScale) * Real.sin (theta j / 2) ^ 2

attribute [instance] GraphCycleLatticeLeyangPhasePackage.instFintypeMode

namespace GraphCycleLatticeLeyangPhasePackage

/-- Every explicit Lee--Yang phase `exp(i θ_j)` lies on the complex unit circle. -/
def unitCircleZeros (P : GraphCycleLatticeLeyangPhasePackage) : Prop :=
  ∀ j : P.Mode, ‖Complex.exp (P.theta j * Complex.I)‖ = 1

/-- The weighted tree polynomial equals the phase product
`|V|^{-1} ∏ (4 D sin²(θ_j/2))`. -/
def phaseTreeFormula (P : GraphCycleLatticeLeyangPhasePackage) : Prop :=
  GraphCycleLatticeWeightedDiscriminantData.reciprocalTreePolynomial P.weighted =
    ((P.vertexCount : ℝ)⁻¹) *
      ∏ j : P.Mode, ((4 * P.phaseScale) * Real.sin (P.theta j / 2) ^ 2)

/-- Multiplying by the full edge-weight product recovers the discriminant in phase form. -/
def discriminantPhaseFormula (P : GraphCycleLatticeLeyangPhasePackage) : Prop :=
  GraphCycleLatticeWeightedDiscriminantData.gramDet P.weighted =
    P.weighted.edgeWeightProduct *
      (((P.vertexCount : ℝ)⁻¹) *
        ∏ j : P.Mode, ((4 * P.phaseScale) * Real.sin (P.theta j / 2) ^ 2))

end GraphCycleLatticeLeyangPhasePackage

open GraphCycleLatticeLeyangPhasePackage

/-- The Lee--Yang phase package puts the nontrivial zeros on the unit circle, rewrites the tree
product through `λ_j = 4 D sin²(θ_j/2)`, and combines with the weighted discriminant identity.
    prop:graph-cycle-lattice-leyang-phase-polynomial -/
theorem paper_graph_cycle_lattice_leyang_phase_polynomial
    (P : GraphCycleLatticeLeyangPhasePackage) :
    GraphCycleLatticeLeyangPhasePackage.unitCircleZeros P ∧
      GraphCycleLatticeLeyangPhasePackage.phaseTreeFormula P ∧
      GraphCycleLatticeLeyangPhasePackage.discriminantPhaseFormula P := by
  refine ⟨?_, ?_, ?_⟩
  · intro j
    simp [Complex.norm_exp]
  · rw [GraphCycleLatticeLeyangPhasePackage.phaseTreeFormula, P.treePolynomial_eq]
    refine congrArg (((P.vertexCount : ℝ)⁻¹) * ·) ?_
    refine Finset.prod_congr rfl ?_
    intro j hj
    rw [P.phaseCompat j]
  · rw [GraphCycleLatticeLeyangPhasePackage.discriminantPhaseFormula]
    calc
      GraphCycleLatticeWeightedDiscriminantData.gramDet P.weighted
          = P.weighted.edgeWeightProduct *
              GraphCycleLatticeWeightedDiscriminantData.reciprocalTreePolynomial P.weighted := by
                exact paper_graph_cycle_lattice_weighted_discriminant P.weighted
      _ = P.weighted.edgeWeightProduct *
            (((P.vertexCount : ℝ)⁻¹) *
              ∏ j : P.Mode, ((4 * P.phaseScale) * Real.sin (P.theta j / 2) ^ 2)) := by
            rw [P.treePolynomial_eq]
            have hprod :
                (∏ j : P.Mode, P.laplacianEigenvalue j) =
                  ∏ j : P.Mode, ((4 * P.phaseScale) * Real.sin (P.theta j / 2) ^ 2) := by
              refine Finset.prod_congr rfl ?_
              intro j hj
              rw [P.phaseCompat j]
            rw [hprod]

end Omega.SPG
