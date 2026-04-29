import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic
import Omega.Graph.TransferMatrix

namespace Omega.POM

open scoped BigOperators

noncomputable section

/-- The two local Fibonacci eigenvectors, with `false` denoting `v⁺ = (φ,1)` and `true`
denoting `v⁻ = (1,-φ)`. -/
def pom_replica_softcore_tensor_eigenbasis_localVector (negative : Bool) : Fin 2 → ℝ
  | 0 => if negative then 1 else Real.goldenRatio
  | 1 => if negative then -Real.goldenRatio else 1

/-- The corresponding local eigenvalues of the Fibonacci kernel. -/
def pom_replica_softcore_tensor_eigenbasis_localEigenvalue (negative : Bool) : ℝ :=
  if negative then 1 - Real.goldenRatio else Real.goldenRatio

/-- The coordinate form of `K^{⊗q}` on the Boolean tensor basis. -/
def pom_replica_softcore_tensor_eigenbasis_tensorKernel (q : ℕ)
    (x y : Fin q → Fin 2) : ℝ :=
  ∏ i, Omega.Graph.goldenMeanAdjacencyℝ (x i) (y i)

/-- Matrix action of the coordinate tensor kernel. -/
def pom_replica_softcore_tensor_eigenbasis_tensorApply (q : ℕ)
    (f : (Fin q → Fin 2) → ℝ) (x : Fin q → Fin 2) : ℝ :=
  ∑ y, pom_replica_softcore_tensor_eigenbasis_tensorKernel q x y * f y

/-- Tensor vector indexed by a subset of negative local eigenvector positions. -/
def pom_replica_softcore_tensor_eigenbasis_tensorVector (q : ℕ) (S : Finset (Fin q))
    (x : Fin q → Fin 2) : ℝ :=
  ∏ i, pom_replica_softcore_tensor_eigenbasis_localVector (i ∈ S) (x i)

/-- The product eigenvalue attached to the tensor vector indexed by `S`. -/
def pom_replica_softcore_tensor_eigenbasis_subsetEigenvalue (q : ℕ)
    (S : Finset (Fin q)) : ℝ :=
  ∏ i, pom_replica_softcore_tensor_eigenbasis_localEigenvalue (i ∈ S)

/-- The common eigenvalue on the fixed layer `|S| = j`. -/
def pom_replica_softcore_tensor_eigenbasis_layerEigenvalue (q j : ℕ) : ℝ :=
  (1 - Real.goldenRatio) ^ j * Real.goldenRatio ^ (q - j)

lemma pom_replica_softcore_tensor_eigenbasis_golden_inv_sub_one :
    (Real.goldenRatio⁻¹ : ℝ) = Real.goldenRatio - 1 := by
  have hinv_conj : (Real.goldenRatio⁻¹ : ℝ) = -Real.goldenConj := by
    simpa [one_div] using Real.inv_goldenRatio
  nlinarith [hinv_conj, Real.goldenRatio_add_goldenConj]

lemma pom_replica_softcore_tensor_eigenbasis_local_eigen
    (negative : Bool) (x : Fin 2) :
    (∑ y : Fin 2,
        Omega.Graph.goldenMeanAdjacencyℝ x y *
          pom_replica_softcore_tensor_eigenbasis_localVector negative y) =
      pom_replica_softcore_tensor_eigenbasis_localEigenvalue negative *
        pom_replica_softcore_tensor_eigenbasis_localVector negative x := by
  rw [Omega.Graph.goldenMeanAdjacencyℝ_eq]
  cases negative <;> fin_cases x
  · simp [pom_replica_softcore_tensor_eigenbasis_localVector,
      pom_replica_softcore_tensor_eigenbasis_localEigenvalue, Fin.sum_univ_two]
    have hsq : Real.goldenRatio * Real.goldenRatio = Real.goldenRatio + 1 := by
      rw [← pow_two]
      exact Real.goldenRatio_sq
    exact hsq.symm
  · simp [pom_replica_softcore_tensor_eigenbasis_localVector,
      pom_replica_softcore_tensor_eigenbasis_localEigenvalue, Fin.sum_univ_two]
  · simp [pom_replica_softcore_tensor_eigenbasis_localVector,
      pom_replica_softcore_tensor_eigenbasis_localEigenvalue, Fin.sum_univ_two]
    ring_nf
  · simp [pom_replica_softcore_tensor_eigenbasis_localVector,
      pom_replica_softcore_tensor_eigenbasis_localEigenvalue, Fin.sum_univ_two]
    have hsq : Real.goldenRatio * Real.goldenRatio = Real.goldenRatio + 1 := by
      rw [← pow_two]
      exact Real.goldenRatio_sq
    nlinarith [hsq]

lemma pom_replica_softcore_tensor_eigenbasis_subsetEigenvalue_eq_layer
    {q : ℕ} {S : Finset (Fin q)} {j : ℕ} (hS : S.card = j) :
    pom_replica_softcore_tensor_eigenbasis_subsetEigenvalue q S =
      pom_replica_softcore_tensor_eigenbasis_layerEigenvalue q j := by
  classical
  rw [pom_replica_softcore_tensor_eigenbasis_subsetEigenvalue,
    pom_replica_softcore_tensor_eigenbasis_layerEigenvalue]
  have hfilter :
      (Finset.univ.filter fun i : Fin q => i ∈ S) = S := by
    ext i
    simp
  have hfilter_not :
      (Finset.univ.filter fun i : Fin q => ¬ i ∈ S) = Sᶜ := by
    ext i
    simp
  rw [← Finset.prod_filter_mul_prod_filter_not (s := Finset.univ)
    (p := fun i : Fin q => i ∈ S)
    (f := fun i : Fin q =>
      pom_replica_softcore_tensor_eigenbasis_localEigenvalue (i ∈ S))]
  rw [hfilter, hfilter_not]
  have hprodS :
      (∏ x ∈ S, pom_replica_softcore_tensor_eigenbasis_localEigenvalue (x ∈ S)) =
        (1 - Real.goldenRatio) ^ S.card := by
    rw [← Finset.prod_const]
    refine Finset.prod_congr rfl ?_
    intro x hx
    simp [pom_replica_softcore_tensor_eigenbasis_localEigenvalue, hx]
  have hprodC :
      (∏ x ∈ Sᶜ, pom_replica_softcore_tensor_eigenbasis_localEigenvalue (x ∈ S)) =
        Real.goldenRatio ^ (q - S.card) := by
    have hcardC : (Sᶜ).card = q - S.card := by
      simp [Finset.card_compl]
    rw [← hcardC]
    rw [← Finset.prod_const]
    refine Finset.prod_congr rfl ?_
    intro x hx
    have hxS : x ∉ S := by
      simpa using hx
    simp [pom_replica_softcore_tensor_eigenbasis_localEigenvalue, hxS]
  rw [hprodS, hprodC, hS]

lemma pom_replica_softcore_tensor_eigenbasis_tensor_eigen
    (q : ℕ) (S : Finset (Fin q)) (x : Fin q → Fin 2) :
    pom_replica_softcore_tensor_eigenbasis_tensorApply q
        (pom_replica_softcore_tensor_eigenbasis_tensorVector q S) x =
      pom_replica_softcore_tensor_eigenbasis_subsetEigenvalue q S *
        pom_replica_softcore_tensor_eigenbasis_tensorVector q S x := by
  classical
  calc
    pom_replica_softcore_tensor_eigenbasis_tensorApply q
        (pom_replica_softcore_tensor_eigenbasis_tensorVector q S) x
        = ∑ y : Fin q → Fin 2,
            ∏ i,
              Omega.Graph.goldenMeanAdjacencyℝ (x i) (y i) *
                pom_replica_softcore_tensor_eigenbasis_localVector (i ∈ S) (y i) := by
          simp [pom_replica_softcore_tensor_eigenbasis_tensorApply,
            pom_replica_softcore_tensor_eigenbasis_tensorKernel,
            pom_replica_softcore_tensor_eigenbasis_tensorVector, Finset.prod_mul_distrib]
    _ = ∏ i,
          ∑ a : Fin 2,
            Omega.Graph.goldenMeanAdjacencyℝ (x i) a *
              pom_replica_softcore_tensor_eigenbasis_localVector (i ∈ S) a := by
          rw [Fintype.prod_sum]
    _ = ∏ i,
          pom_replica_softcore_tensor_eigenbasis_localEigenvalue (i ∈ S) *
            pom_replica_softcore_tensor_eigenbasis_localVector (i ∈ S) (x i) := by
          congr 1
          ext i
          exact pom_replica_softcore_tensor_eigenbasis_local_eigen (i ∈ S) (x i)
    _ = pom_replica_softcore_tensor_eigenbasis_subsetEigenvalue q S *
          pom_replica_softcore_tensor_eigenbasis_tensorVector q S x := by
          simp [pom_replica_softcore_tensor_eigenbasis_subsetEigenvalue,
            pom_replica_softcore_tensor_eigenbasis_tensorVector, Finset.prod_mul_distrib]

/-- Concrete paper-facing package for the Fibonacci `2 × 2` kernel tensor eigenbasis. -/
def pom_replica_softcore_tensor_eigenbasis_statement (q : Nat) : Prop :=
  (1 - Real.goldenRatio = -Real.goldenRatio⁻¹) ∧
    (∀ x : Fin 2,
      (∑ y : Fin 2,
          Omega.Graph.goldenMeanAdjacencyℝ x y *
            pom_replica_softcore_tensor_eigenbasis_localVector false y) =
        Real.goldenRatio * pom_replica_softcore_tensor_eigenbasis_localVector false x) ∧
    (∀ x : Fin 2,
      (∑ y : Fin 2,
          Omega.Graph.goldenMeanAdjacencyℝ x y *
            pom_replica_softcore_tensor_eigenbasis_localVector true y) =
        (1 - Real.goldenRatio) *
          pom_replica_softcore_tensor_eigenbasis_localVector true x) ∧
    (∀ S : Finset (Fin q), ∀ x : Fin q → Fin 2,
      pom_replica_softcore_tensor_eigenbasis_tensorApply q
          (pom_replica_softcore_tensor_eigenbasis_tensorVector q S) x =
        pom_replica_softcore_tensor_eigenbasis_subsetEigenvalue q S *
          pom_replica_softcore_tensor_eigenbasis_tensorVector q S x) ∧
    (∀ j : ℕ, ∀ S : Finset (Fin q), S.card = j →
      pom_replica_softcore_tensor_eigenbasis_subsetEigenvalue q S =
        pom_replica_softcore_tensor_eigenbasis_layerEigenvalue q j)

/-- Paper label: `thm:pom-replica-softcore-tensor-eigenbasis`. -/
theorem paper_pom_replica_softcore_tensor_eigenbasis (q : Nat) :
    pom_replica_softcore_tensor_eigenbasis_statement q := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [pom_replica_softcore_tensor_eigenbasis_golden_inv_sub_one]
    ring
  · intro x
    simpa [pom_replica_softcore_tensor_eigenbasis_localEigenvalue] using
      pom_replica_softcore_tensor_eigenbasis_local_eigen false x
  · intro x
    simpa [pom_replica_softcore_tensor_eigenbasis_localEigenvalue] using
      pom_replica_softcore_tensor_eigenbasis_local_eigen true x
  · intro S x
    exact pom_replica_softcore_tensor_eigenbasis_tensor_eigen q S x
  · intro j S hS
    exact pom_replica_softcore_tensor_eigenbasis_subsetEigenvalue_eq_layer hS

end

end Omega.POM
