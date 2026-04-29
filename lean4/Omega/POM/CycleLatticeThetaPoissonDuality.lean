import Mathlib.Tactic
import Omega.Graph.FlowLatticeGramDeterminantTreeWeight
import Omega.SPG.GraphCycleLatticeDeterminantPrimeSupport
import Omega.SPG.GraphCycleLatticeLeyangPhasePolynomial

namespace Omega.POM

open Omega.Graph
open Omega.SPG
open GraphCycleLatticeWeightedDiscriminantData
open GraphCycleLatticeLeyangPhasePackage
open GraphCycleLatticeDeterminantPrimeSupportData

/-- Concrete data for the cycle-lattice theta/Poisson package. The phase model records the
nonzero Laplacian modes, the determinant package records the Smith-normal-form torsion data, and
the auxiliary flow graph carries the tree-normalized Gram determinant. -/
structure CycleLatticeThetaPoissonDualityData where
  phase : GraphCycleLatticeLeyangPhasePackage
  determinant : GraphCycleLatticeDeterminantPrimeSupportData
  flowGraph : FlowWeightedMultigraph
  graphConnected : flowGraph.Connected
  weightedTreeSum_eq :
    flowGraph.weightedTreeSum = reciprocalTreePolynomial phase.weighted
  edgeWeightDet_eq :
    flowGraph.edgeWeightDet = phase.weighted.edgeWeightProduct
  poissonScale : ℝ

namespace CycleLatticeThetaPoissonDualityData

/-- The Gaussian bulk theta term written through the cycle-lattice Gram determinant. -/
noncomputable def thetaBulk (D : CycleLatticeThetaPoissonDualityData) : ℝ :=
  D.poissonScale * gramDet D.phase.weighted

/-- The dual theta term written through the weighted spanning-tree normalization. -/
noncomputable def thetaDual (D : CycleLatticeThetaPoissonDualityData) : ℝ :=
  D.poissonScale *
    (D.phase.weighted.edgeWeightProduct * reciprocalTreePolynomial D.phase.weighted)

/-- The tree-normalized Gram determinant coming from the auxiliary flow-lattice model. -/
noncomputable def treeNormalizedGram (D : CycleLatticeThetaPoissonDualityData) : ℝ :=
  flowLatticeGramDet D.flowGraph

/-- The corresponding weighted reciprocal-tree ratio. -/
noncomputable def weightedTreeRatio (D : CycleLatticeThetaPoissonDualityData) : ℝ :=
  reciprocalTreePolynomial D.phase.weighted / D.phase.weighted.edgeWeightProduct

end CycleLatticeThetaPoissonDualityData

open CycleLatticeThetaPoissonDualityData

/-- Package theorem for cycle-lattice theta/Poisson duality: the bulk and dual theta terms agree
by the weighted discriminant identity, the Lee--Yang phase polynomial keeps the zeros on the unit
circle and identifies the tree polynomial, the flow-lattice Gram determinant is the same
tree-normalized ratio, and the determinant package identifies the torsion size and prime support.
-/
def CycleLatticeThetaPoissonDuality (D : CycleLatticeThetaPoissonDualityData) : Prop :=
  thetaBulk D = thetaDual D ∧
    unitCircleZeros D.phase ∧
    phaseTreeFormula D.phase ∧
    discriminantPhaseFormula D.phase ∧
    treeNormalizedGram D = weightedTreeRatio D ∧
    D.determinant.kernelCardinalityEqualsDeterminant ∧
    D.determinant.primeSupportMatchesDeterminant

/-- Paper label: `thm:pom-cycle-lattice-theta-poisson-duality`. -/
theorem paper_pom_cycle_lattice_theta_poisson_duality
    (D : CycleLatticeThetaPoissonDualityData) : CycleLatticeThetaPoissonDuality D := by
  have hWeight := paper_graph_cycle_lattice_weighted_discriminant D.phase.weighted
  have hPhase := paper_graph_cycle_lattice_leyang_phase_polynomial D.phase
  have hFlow := paper_xi_flow_lattice_gram_determinant_tree_weight D.flowGraph D.graphConnected
  have hPrime := paper_graph_cycle_lattice_determinant_prime_support D.determinant
  refine ⟨?_, hPhase.1, hPhase.2.1, hPhase.2.2, ?_, hPrime.1, hPrime.2⟩
  · simpa [thetaBulk, thetaDual] using congrArg (fun x : ℝ => D.poissonScale * x) hWeight
  · unfold treeNormalizedGram weightedTreeRatio
    rw [hFlow, D.weightedTreeSum_eq, D.edgeWeightDet_eq]

end Omega.POM
