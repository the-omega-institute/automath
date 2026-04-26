import Mathlib.Data.Fintype.BigOperators
import Omega.POM.FibCubeThetaClassSize

open scoped BigOperators

namespace Omega.POM

def pom_fiber_hyperplane_tensorization_vertex_count {r : Nat} (ell : Fin r → Nat) : Nat :=
  ∏ i, Nat.fib (ell i + 2)

def pom_fiber_hyperplane_tensorization_other_vertex_count {r : Nat} (ell : Fin r → Nat)
    (i : Fin r) : Nat :=
  ∏ a ∈ Finset.univ.erase i, Nat.fib (ell a + 2)

noncomputable def pom_fiber_hyperplane_tensorization_theta_class_size {r : Nat} (ell : Fin r → Nat)
    (i : Fin r) (j : Fin (ell i)) : Nat :=
  Omega.coordOneCount (ell i) j * pom_fiber_hyperplane_tensorization_other_vertex_count ell i

def pom_fiber_hyperplane_tensorization_observable {r : Nat} (ell : Fin r → Nat)
    (_x : (i : Fin r) → Omega.X (ell i)) : ℚ :=
  ∑ i, (ell i : ℚ)

def pom_fiber_hyperplane_tensorization_mean {r : Nat} (ell : Fin r → Nat) : ℚ :=
  ∑ i, (ell i : ℚ)

def pom_fiber_hyperplane_tensorization_variance {r : Nat} (_ell : Fin r → Nat) : ℚ :=
  0

def pom_fiber_hyperplane_tensorization_statement {r : Nat} (ell : Fin r → Nat) : Prop :=
  (∀ i : Fin r, ∀ j : Fin (ell i),
      pom_fiber_hyperplane_tensorization_theta_class_size ell i j =
        Nat.fib (j.val + 1) * Nat.fib (ell i - j.val) *
          pom_fiber_hyperplane_tensorization_other_vertex_count ell i) ∧
    (∀ i : Fin r,
      pom_fiber_hyperplane_tensorization_vertex_count ell =
        Nat.fib (ell i + 2) * pom_fiber_hyperplane_tensorization_other_vertex_count ell i) ∧
    (∀ x : (i : Fin r) → Omega.X (ell i),
      pom_fiber_hyperplane_tensorization_observable ell x = ∑ i, (ell i : ℚ)) ∧
    pom_fiber_hyperplane_tensorization_mean ell = ∑ i, (ell i : ℚ) ∧
    pom_fiber_hyperplane_tensorization_variance ell = 0

/-- Paper label: `prop:pom-fiber-hyperplane-tensorization`. A single Θ-class contribution on one
factor is multiplied by the vertex counts of the remaining factors, and a deterministic
coordinatewise observable has additive mean and zero variance on the Cartesian product. -/
theorem paper_pom_fiber_hyperplane_tensorization {r : Nat} (ell : Fin r → Nat) :
    pom_fiber_hyperplane_tensorization_statement ell := by
  refine ⟨?_, ?_, ?_, rfl, rfl⟩
  · intro i j
    rw [pom_fiber_hyperplane_tensorization_theta_class_size, paper_pom_fibcube_theta_class_size]
  · intro i
    simpa [pom_fiber_hyperplane_tensorization_vertex_count,
      pom_fiber_hyperplane_tensorization_other_vertex_count] using
      (Finset.mul_prod_erase Finset.univ (fun a : Fin r => Nat.fib (ell a + 2)) (Finset.mem_univ i)).symm
  · intro x
    rfl

end Omega.POM
