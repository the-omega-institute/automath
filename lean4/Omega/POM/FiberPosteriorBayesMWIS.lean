import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.POM

open scoped BigOperators

section FinsetLoss

variable {α : Type*} [DecidableEq α]

/-- Symmetric-difference cardinality written additively over the two set differences. -/
def symmetricDifferenceCard (A B : Finset α) : ℝ :=
  (((A \ B).card + (B \ A).card : ℕ) : ℝ)

/-- The paper's Hamming-side loss carries an overall factor `3`. -/
def threeHammingLoss (A B : Finset α) : ℝ :=
  (3 : ℝ) * symmetricDifferenceCard A B

/-- An independent set on a path component cannot contain both endpoints of any adjacent pair in
the path-order listing. -/
def pathComponentIndependent (component : List α) (A : Finset α) : Prop :=
  ∀ edge ∈ component.zip component.tail, edge.1 ∉ A ∨ edge.2 ∉ A

/-- Independence on a disjoint union of path components is checked componentwise. -/
def pathIndependent (components : List (List α)) (A : Finset α) : Prop :=
  ∀ component ∈ components, pathComponentIndependent component A

/-- Vertex score induced by the posterior marginal in the factor-`3` loss normalization. -/
def posteriorVertexWeight (μ : α → ℝ) (v : α) : ℝ :=
  6 * μ v - 3

/-- Total posterior weight of a candidate independent set. -/
def totalPosteriorWeight (μ : α → ℝ) (A : Finset α) : ℝ :=
  Finset.sum A (fun v => posteriorVertexWeight μ v)

end FinsetLoss

/-- Concrete posterior-marginal data for the path-component Bayes/MWIS reduction. The decoder is
assumed to be an independent set maximizing the posterior vertex weights over the admissible path
components. -/
structure FiberPosteriorBayesMWISData where
  n : ℕ
  pathComponents : List (List (Fin n))
  posteriorMarginal : Fin n → ℝ
  decoder : Finset (Fin n)
  decoderIndependent : pathIndependent pathComponents decoder
  mwisOptimal :
    ∀ A : Finset (Fin n), pathIndependent pathComponents A →
      totalPosteriorWeight posteriorMarginal A ≤
        totalPosteriorWeight posteriorMarginal decoder

namespace FiberPosteriorBayesMWISData

/-- The constant term in the posterior expected loss once the vertexwise marginals are expanded. -/
def lossConstant (D : FiberPosteriorBayesMWISData) : ℝ :=
  Finset.sum Finset.univ (fun v : Fin D.n => 3 * D.posteriorMarginal v)

/-- The MWIS objective obtained from the posterior marginals. -/
def vertexWeight (D : FiberPosteriorBayesMWISData) (v : Fin D.n) : ℝ :=
  posteriorVertexWeight D.posteriorMarginal v

/-- Total decoder weight in the MWIS reduction. -/
def totalVertexWeight (D : FiberPosteriorBayesMWISData) (A : Finset (Fin D.n)) : ℝ :=
  totalPosteriorWeight D.posteriorMarginal A

/-- Expected factor-`3` symmetric-difference loss written as a sum of one-vertex marginals. -/
def posteriorExpectedLoss (D : FiberPosteriorBayesMWISData) (A : Finset (Fin D.n)) : ℝ :=
  Finset.sum Finset.univ
    (fun v : Fin D.n => if v ∈ A then 3 * (1 - D.posteriorMarginal v) else 3 * D.posteriorMarginal v)

/-- Bayes-optimal decoding is equivalent to solving the posterior-weight MWIS problem on the path
components. The conjunction records the factor-`3` Hamming/symmetric-difference identity, the
vertex-marginal loss expansion, and the resulting optimality statement for the chosen decoder. -/
def bayesOptimalAsMaximumWeightIndependentSet (D : FiberPosteriorBayesMWISData) : Prop :=
  (∀ A B : Finset (Fin D.n), threeHammingLoss A B = (3 : ℝ) * symmetricDifferenceCard A B) ∧
    (∀ A : Finset (Fin D.n),
      D.posteriorExpectedLoss A = D.lossConstant - D.totalVertexWeight A) ∧
    pathIndependent D.pathComponents D.decoder ∧
    ∀ A : Finset (Fin D.n), pathIndependent D.pathComponents A →
      D.posteriorExpectedLoss D.decoder ≤ D.posteriorExpectedLoss A

lemma posteriorExpectedLoss_eq_constant_sub_weight
    (D : FiberPosteriorBayesMWISData) (A : Finset (Fin D.n)) :
    D.posteriorExpectedLoss A = D.lossConstant - D.totalVertexWeight A := by
  classical
  have hterm :
      ∀ v : Fin D.n,
        (if v ∈ A then 3 * (1 - D.posteriorMarginal v) else 3 * D.posteriorMarginal v) =
          3 * D.posteriorMarginal v - (if v ∈ A then D.vertexWeight v else 0) := by
    intro v
    by_cases hv : v ∈ A
    · simp [hv, vertexWeight, posteriorVertexWeight]
      ring
    · simp [hv]
  calc
    D.posteriorExpectedLoss A
      = Finset.sum Finset.univ
          (fun v : Fin D.n => 3 * D.posteriorMarginal v - if v ∈ A then D.vertexWeight v else 0) := by
            unfold posteriorExpectedLoss
            refine Finset.sum_congr rfl ?_
            intro v hv
            exact hterm v
    _ = Finset.sum Finset.univ (fun v : Fin D.n => 3 * D.posteriorMarginal v) -
          Finset.sum Finset.univ (fun v : Fin D.n => if v ∈ A then D.vertexWeight v else 0) := by
            rw [Finset.sum_sub_distrib]
    _ = D.lossConstant - D.totalVertexWeight A := by
          rw [Finset.sum_ite_mem_eq]
          simp [lossConstant, totalVertexWeight, totalPosteriorWeight, vertexWeight]

end FiberPosteriorBayesMWISData

open FiberPosteriorBayesMWISData

/-- The factor-`3` loss agrees with three times the symmetric-difference penalty; expanding the
posterior risk by vertex marginals produces a constant minus the posterior MWIS objective; hence a
maximum-weight independent set on the path components is Bayes-optimal.
    thm:pom-fiber-posterior-bayes-mwis -/
theorem paper_pom_fiber_posterior_bayes_mwis (D : FiberPosteriorBayesMWISData) :
    D.bayesOptimalAsMaximumWeightIndependentSet := by
  refine ⟨?_, ?_, D.decoderIndependent, ?_⟩
  · intro A B
    rfl
  · intro A
    exact D.posteriorExpectedLoss_eq_constant_sub_weight A
  · intro A hA
    rw [D.posteriorExpectedLoss_eq_constant_sub_weight D.decoder,
      D.posteriorExpectedLoss_eq_constant_sub_weight A]
    exact sub_le_sub_left (D.mwisOptimal A hA) D.lossConstant

end Omega.POM
