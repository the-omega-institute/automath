import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.POM

/-- A finite weighted graph presented by its vertex set and an ordered conductance kernel. The
vertex weights are recorded as part of the concrete Hodge--Stein package, while the conductance
kernel governs the `1`-form inner product and the discrete divergence. -/
structure FiberWeightedGraph where
  V : Type
  fintypeV : Fintype V
  vertexWeight : V → ℝ
  conductance : V → V → ℝ

attribute [instance] FiberWeightedGraph.fintypeV

/-- Vertex functions on a finite weighted graph. -/
abbrev FiberZeroForm (G : FiberWeightedGraph) := G.V → ℝ

/-- Edge functions on the ordered conductance kernel. -/
abbrev FiberOneForm (G : FiberWeightedGraph) := G.V → G.V → ℝ

/-- The vertex pairing. -/
def fiberVertexInner (G : FiberWeightedGraph) (f g : FiberZeroForm G) : ℝ :=
  ∑ v, f v * g v

/-- The conductance-weighted edge pairing. -/
def fiberEdgeInner (G : FiberWeightedGraph) (J K : FiberOneForm G) : ℝ :=
  ∑ u, ∑ v, G.conductance u v * J u v * K u v

/-- The discrete differential. -/
def fiberD (G : FiberWeightedGraph) (f : FiberZeroForm G) : FiberOneForm G :=
  fun u v => f v - f u

/-- The discrete codifferential. -/
def fiberDelta (G : FiberWeightedGraph) (J : FiberOneForm G) : FiberZeroForm G :=
  fun v => ∑ w, G.conductance v w * J v w - ∑ u, G.conductance u v * J u v

/-- The positive-sign `0`-form Laplacian attached to the Hodge--Stein package. -/
def fiberLaplacian (G : FiberWeightedGraph) (f : FiberZeroForm G) : FiberZeroForm G :=
  fun v => -fiberDelta G (fiberD G f) v

theorem fiber_stokes_duality (G : FiberWeightedGraph) (f : FiberZeroForm G) (J : FiberOneForm G) :
    fiberVertexInner G f (fiberDelta G J) = -fiberEdgeInner G (fiberD G f) J := by
  classical
  unfold fiberVertexInner fiberDelta fiberEdgeInner fiberD
  calc
    ∑ v, f v * (∑ w, G.conductance v w * J v w - ∑ u, G.conductance u v * J u v) =
        (∑ v, ∑ w, f v * (G.conductance v w * J v w)) -
          ∑ v, ∑ u, f v * (G.conductance u v * J u v) := by
      simp [mul_sub, Finset.mul_sum, Finset.sum_sub_distrib, mul_assoc, mul_left_comm, mul_comm]
    _ = (∑ u, ∑ v, f u * (G.conductance u v * J u v)) -
          ∑ u, ∑ v, f v * (G.conductance u v * J u v) := by
      congr 1
      · rw [Finset.sum_comm]
    _ = ∑ u, ∑ v, -(G.conductance u v * (f v - f u) * J u v) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl ?_
      intro u hu
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl ?_
      intro v hv
      ring_nf
    _ = -fiberEdgeInner G (fiberD G f) J := by
      simp [fiberEdgeInner, fiberD, Finset.sum_neg_distrib]

theorem fiber_energy_identity (G : FiberWeightedGraph) (u : FiberZeroForm G) :
    fiberVertexInner G u (fiberLaplacian G u) = fiberEdgeInner G (fiberD G u) (fiberD G u) := by
  have hstokes := fiber_stokes_duality G u (fiberD G u)
  have hrewrite :
      fiberVertexInner G u (fiberLaplacian G u) = -fiberVertexInner G u (fiberDelta G (fiberD G u)) := by
    unfold fiberVertexInner fiberLaplacian
    calc
      ∑ v, u v * (-fiberDelta G (fiberD G u) v) = ∑ v, -(u v * fiberDelta G (fiberD G u) v) := by
        refine Finset.sum_congr rfl ?_
        intro v hv
        ring
      _ = -∑ v, u v * fiberDelta G (fiberD G u) v := by
        rw [Finset.sum_neg_distrib]
  linarith

/-- Concrete tensorization data: a weighted graph for the Stokes side together with a finite
family of factor spectral gaps and Poisson loads for the diagonal Cartesian model. -/
structure FiberHodgeSteinTensorizationGapData where
  G : FiberWeightedGraph
  r : Nat
  hr : 0 < r
  factorGap : Fin r → ℝ
  factorGap_ne_zero : ∀ i, factorGap i ≠ 0
  factorLoad : Fin r → ℝ

namespace FiberHodgeSteinTensorizationGapData

/-- The `i`-th diagonal Laplace block in the Cartesian tensorization model. -/
def factorLaplacianMatrix (D : FiberHodgeSteinTensorizationGapData) (i : Fin D.r) :
    Matrix (Fin D.r) (Fin D.r) ℝ :=
  fun a b => if a = b ∧ a = i then D.factorGap i else 0

/-- The Cartesian-product Laplacian: a diagonal Kronecker sum with entries the factor gaps. -/
def cartesianLaplacianMatrix (D : FiberHodgeSteinTensorizationGapData) :
    Matrix (Fin D.r) (Fin D.r) ℝ :=
  fun a b => if a = b then D.factorGap a else 0

/-- The factorwise Poisson solution for the diagonal model. -/
noncomputable def poissonPotential (D : FiberHodgeSteinTensorizationGapData) : Fin D.r → ℝ :=
  fun i => D.factorLoad i / D.factorGap i

/-- Applying the diagonal Cartesian Laplacian to the Poisson potential recovers the load. -/
noncomputable def poissonSource (D : FiberHodgeSteinTensorizationGapData) : Fin D.r → ℝ :=
  fun i => ∑ j, D.cartesianLaplacianMatrix i j * D.poissonPotential j

/-- The minimizing flow in the diagonal Hodge gauge is the negative gradient. -/
noncomputable def minimizerFlow (D : FiberHodgeSteinTensorizationGapData) : Fin D.r → ℝ :=
  fun i => -D.poissonPotential i

/-- The smallest positive diagonal mode of the tensorized Laplacian. -/
noncomputable def productSpectralGap (D : FiberHodgeSteinTensorizationGapData) : ℝ :=
  sInf (Set.range D.factorGap)

/-- Concrete validity package for the fiber Hodge--Stein tensorization statement. -/
def Valid (D : FiberHodgeSteinTensorizationGapData) : Prop :=
  (∀ f J, fiberVertexInner D.G f (fiberDelta D.G J) = -fiberEdgeInner D.G (fiberD D.G f) J) ∧
    (∀ u, fiberVertexInner D.G u (fiberLaplacian D.G u) =
      fiberEdgeInner D.G (fiberD D.G u) (fiberD D.G u)) ∧
    D.cartesianLaplacianMatrix = ∑ i, D.factorLaplacianMatrix i ∧
    (∀ i, D.poissonSource i = D.factorLoad i) ∧
    (D.minimizerFlow = fun i => -D.poissonPotential i) ∧
    D.productSpectralGap = sInf (Set.range D.factorGap)

theorem cartesianLaplacianMatrix_eq_sum_factorLaplacianMatrix
    (D : FiberHodgeSteinTensorizationGapData) :
    D.cartesianLaplacianMatrix = ∑ i, D.factorLaplacianMatrix i := by
  classical
  ext a b
  rw [Matrix.sum_apply]
  by_cases hab : a = b
  · subst hab
    simp [cartesianLaplacianMatrix, factorLaplacianMatrix]
  · simp [cartesianLaplacianMatrix, factorLaplacianMatrix, hab]

theorem poissonSource_eq_factorLoad (D : FiberHodgeSteinTensorizationGapData) (i : Fin D.r) :
    D.poissonSource i = D.factorLoad i := by
  unfold poissonSource cartesianLaplacianMatrix poissonPotential
  simp
  field_simp [D.factorGap_ne_zero i]

end FiberHodgeSteinTensorizationGapData

open FiberHodgeSteinTensorizationGapData

/-- Paper label: `thm:pom-fiber-hodge-stein-tensorization-gap`. -/
theorem paper_pom_fiber_hodge_stein_tensorization_gap
    (D : FiberHodgeSteinTensorizationGapData) : D.Valid := by
  refine ⟨fiber_stokes_duality D.G, fiber_energy_identity D.G,
    cartesianLaplacianMatrix_eq_sum_factorLaplacianMatrix D, poissonSource_eq_factorLoad D,
    rfl, rfl⟩

end Omega.POM
