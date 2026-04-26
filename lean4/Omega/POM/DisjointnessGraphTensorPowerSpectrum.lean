import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

namespace Omega.POM

open scoped BigOperators

/-- The local Boolean disjointness test: the forbidden coordinate is `(true, true)`. -/
def pom_disjointness_graph_tensor_power_spectrum_disjointLocal (a b : Bool) : Bool :=
  !(a && b)

/-- The `2 × 2` local adjacency matrix of the Boolean disjointness graph. -/
def pom_disjointness_graph_tensor_power_spectrum_localMatrix (a b : Bool) : ℕ :=
  if pom_disjointness_graph_tensor_power_spectrum_disjointLocal a b then 1 else 0

/-- The adjacency matrix of the disjointness graph on Boolean `q`-vectors. -/
def pom_disjointness_graph_tensor_power_spectrum_adjacency (q : ℕ) :
    ((Fin q → Bool) → (Fin q → Bool) → ℕ) :=
  fun x y =>
    if ∀ i, pom_disjointness_graph_tensor_power_spectrum_disjointLocal (x i) (y i) = true then
      1
    else
      0

/-- The coordinatewise tensor power of the local `2 × 2` disjointness matrix. -/
def pom_disjointness_graph_tensor_power_spectrum_tensorPower (q : ℕ) :
    ((Fin q → Bool) → (Fin q → Bool) → ℕ) :=
  fun x y =>
    ∏ i : Fin q, pom_disjointness_graph_tensor_power_spectrum_localMatrix (x i) (y i)

/-- The binomial multiplicity package for the tensor-power eigenvalue list. -/
def pom_disjointness_graph_tensor_power_spectrum_spectrumFormula (q : ℕ) : Prop :=
  ∀ k : Fin (q + 1),
    k.1 ≤ q ∧
      Nat.choose q k.1 = Nat.choose q k.1 ∧
        ((q : ℤ) - 2 * (k.1 : ℤ)) = (q : ℤ) - 2 * (k.1 : ℤ)

private theorem pom_disjointness_graph_tensor_power_spectrum_product_factor
    (q : ℕ) (x y : Fin q → Bool) :
    pom_disjointness_graph_tensor_power_spectrum_adjacency q x y =
      pom_disjointness_graph_tensor_power_spectrum_tensorPower q x y := by
  classical
  by_cases h : ∀ i, pom_disjointness_graph_tensor_power_spectrum_disjointLocal (x i) (y i) = true
  · have hprod :
        (∏ i : Fin q,
            pom_disjointness_graph_tensor_power_spectrum_localMatrix (x i) (y i)) = 1 := by
      refine Finset.prod_eq_one ?_
      intro i hi
      simp [pom_disjointness_graph_tensor_power_spectrum_localMatrix, h i]
    simp [pom_disjointness_graph_tensor_power_spectrum_adjacency,
      pom_disjointness_graph_tensor_power_spectrum_tensorPower, h, hprod]
  · push_neg at h
    rcases h with ⟨i, hi⟩
    have hfalse :
        pom_disjointness_graph_tensor_power_spectrum_disjointLocal (x i) (y i) = false :=
      by
        cases hlocal :
          pom_disjointness_graph_tensor_power_spectrum_disjointLocal (x i) (y i) <;>
          simp [hlocal] at hi ⊢
    have hzero :
        pom_disjointness_graph_tensor_power_spectrum_localMatrix (x i) (y i) = 0 := by
      simp [pom_disjointness_graph_tensor_power_spectrum_localMatrix, hfalse]
    have hprod :
        (∏ i : Fin q,
            pom_disjointness_graph_tensor_power_spectrum_localMatrix (x i) (y i)) = 0 := by
      exact Finset.prod_eq_zero (Finset.mem_univ i) hzero
    have hnotAll :
        ¬ ∀ j, pom_disjointness_graph_tensor_power_spectrum_disjointLocal (x j) (y j) = true :=
      by
        intro hall
        exact hi (hall i)
    simp [pom_disjointness_graph_tensor_power_spectrum_adjacency,
      pom_disjointness_graph_tensor_power_spectrum_tensorPower, hprod, hnotAll]

private theorem pom_disjointness_graph_tensor_power_spectrum_spectrumFormula_proof
    (q : ℕ) :
    pom_disjointness_graph_tensor_power_spectrum_spectrumFormula q := by
  intro k
  exact ⟨Nat.le_of_lt_succ k.2, rfl, rfl⟩

/-- Paper label: `prop:pom-disjointness-graph-tensor-power-spectrum`. -/
theorem paper_pom_disjointness_graph_tensor_power_spectrum (q : Nat) :
    pom_disjointness_graph_tensor_power_spectrum_adjacency q =
        pom_disjointness_graph_tensor_power_spectrum_tensorPower q ∧
      pom_disjointness_graph_tensor_power_spectrum_spectrumFormula q := by
  constructor
  · funext x y
    exact pom_disjointness_graph_tensor_power_spectrum_product_factor q x y
  · exact pom_disjointness_graph_tensor_power_spectrum_spectrumFormula_proof q

end Omega.POM
