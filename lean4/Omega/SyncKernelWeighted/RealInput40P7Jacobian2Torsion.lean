import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Tactic
import Omega.SyncKernelWeighted.RealInput40P7Branch10GaloisS10

namespace Omega.SyncKernelWeighted

open scoped BigOperators

/-- Concrete Jacobian `2`-torsion audit package. A vector in `(𝔽₂)^{10}` models an even subset of
the ten branch points; Galois invariance is recorded through the audited branch action. -/
structure real_input_40_p7_jacobian_2torsion_data where
  branchGaloisData : real_input_40_p7_branch10_galois_s10_data
  fixedVector : Fin 10 → ZMod 2
  fixedVector_even : ∑ i, fixedVector i = 0
  fixedByGalois :
    ∀ σ : Equiv.Perm (Fin 10), σ ∈ branchGaloisData.galoisGroup →
      fixedVector = fixedVector ∘ σ

/-- The even-subset model for `J[2]`: characteristic vectors with even total weight. -/
def real_input_40_p7_jacobian_2torsion_even_subset_model (v : Fin 10 → ZMod 2) : Prop :=
  ∑ i, v i = 0

/-- The zero class in the even-subset model. -/
def real_input_40_p7_jacobian_2torsion_zero_vector : Fin 10 → ZMod 2 :=
  fun _ => 0

/-- The all-ones representative of the complement relation. -/
def real_input_40_p7_jacobian_2torsion_all_ones_vector : Fin 10 → ZMod 2 :=
  fun _ => 1

/-- Quotienting by complements means that only the zero and all-ones representatives remain in the
trivial class. -/
def real_input_40_p7_jacobian_2torsion_quotient_class_vanishes (v : Fin 10 → ZMod 2) : Prop :=
  v = real_input_40_p7_jacobian_2torsion_zero_vector ∨
    v = real_input_40_p7_jacobian_2torsion_all_ones_vector

lemma real_input_40_p7_jacobian_2torsion_all_ones_even :
    real_input_40_p7_jacobian_2torsion_even_subset_model
      real_input_40_p7_jacobian_2torsion_all_ones_vector := by
  unfold real_input_40_p7_jacobian_2torsion_even_subset_model
    real_input_40_p7_jacobian_2torsion_all_ones_vector
  decide

lemma real_input_40_p7_jacobian_2torsion_fixed_coords_equal
    (D : real_input_40_p7_jacobian_2torsion_data) (i j : Fin 10) :
    D.fixedVector i = D.fixedVector j := by
  by_cases hij : i = j
  · simpa [hij]
  · rcases paper_real_input_40_p7_branch10_galois_s10 D.branchGaloisData with
      ⟨_, _, _, _, _, _, _, htop⟩
    have hswap_mem : Equiv.swap i j ∈ D.branchGaloisData.galoisGroup := by
      rw [htop]
      simp
    have hfix :=
      congrArg (fun f : Fin 10 → ZMod 2 => f i) (D.fixedByGalois (Equiv.swap i j) hswap_mem)
    simpa [Function.comp, hij] using hfix

lemma real_input_40_p7_jacobian_2torsion_invariant_class_vanishes
    (D : real_input_40_p7_jacobian_2torsion_data) :
    real_input_40_p7_jacobian_2torsion_quotient_class_vanishes D.fixedVector := by
  by_cases hzero : D.fixedVector 0 = 0
  · left
    funext i
    exact (real_input_40_p7_jacobian_2torsion_fixed_coords_equal D i 0).trans hzero
  · right
    have hclassified : ∀ y : ZMod 2, y = 0 ∨ y = 1 := by
      decide
    have hone : D.fixedVector 0 = 1 := (hclassified (D.fixedVector 0)).resolve_left hzero
    funext i
    exact (real_input_40_p7_jacobian_2torsion_fixed_coords_equal D i 0).trans hone

/-- Paper-facing formulation of the Jacobian `2`-torsion vanishing argument. The preceding
`S₁₀`-package supplies the full permutation action, so an invariant even vector is constant and
hence trivial after quotienting by the all-ones vector. -/
def real_input_40_p7_jacobian_2torsion_statement
    (D : real_input_40_p7_jacobian_2torsion_data) : Prop :=
  real_input_40_p7_branch10_galois_s10_statement D.branchGaloisData ∧
    real_input_40_p7_jacobian_2torsion_even_subset_model D.fixedVector ∧
    real_input_40_p7_jacobian_2torsion_even_subset_model
      real_input_40_p7_jacobian_2torsion_all_ones_vector ∧
    (∀ i j : Fin 10, D.fixedVector i = D.fixedVector j) ∧
    real_input_40_p7_jacobian_2torsion_quotient_class_vanishes D.fixedVector

/-- Paper label: `prop:real-input-40-p7-jacobian-2torsion`. -/
theorem paper_real_input_40_p7_jacobian_2torsion (D : real_input_40_p7_jacobian_2torsion_data) :
    real_input_40_p7_jacobian_2torsion_statement D := by
  refine ⟨paper_real_input_40_p7_branch10_galois_s10 D.branchGaloisData, ?_, ?_, ?_, ?_⟩
  · simpa [real_input_40_p7_jacobian_2torsion_even_subset_model] using D.fixedVector_even
  · exact real_input_40_p7_jacobian_2torsion_all_ones_even
  · intro i j
    exact real_input_40_p7_jacobian_2torsion_fixed_coords_equal D i j
  · exact real_input_40_p7_jacobian_2torsion_invariant_class_vanishes D

end Omega.SyncKernelWeighted
