import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace Omega.GU.ParryEndpointMassMatrix

open Finset
open scoped BigOperators

variable {α ι R : Type*}

/-- The endpoint fiber inside a finite word set. -/
def endpointFiber [DecidableEq α] (words : Finset α) (start finish : α → ι)
    [DecidableEq ι] (i j : ι) : Finset α :=
  words.filter fun u => start u = i ∧ finish u = j

/-- The total endpoint mass of the `(i,j)` fiber. -/
def endpointMass [DecidableEq α] (words : Finset α) (start finish : α → ι)
    [DecidableEq ι] [AddCommMonoid R] (pm : α → R) (i j : ι) : R :=
  Finset.sum (endpointFiber words start finish i j) pm

/-- If the cylinder mass is constant on each endpoint fiber, the endpoint mass is
    cardinality times the common fiber weight. -/
theorem endpointMass_eq_card_mul_of_const [DecidableEq α] [DecidableEq ι] [Semiring R]
    (words : Finset α) (start finish : α → ι) (pm : α → R) (i j : ι) (w : R)
    (hconst : ∀ u ∈ endpointFiber words start finish i j, pm u = w) :
    endpointMass words start finish pm i j = (endpointFiber words start finish i j).card * w := by
  unfold endpointMass
  have hsum :
      Finset.sum (endpointFiber words start finish i j) pm =
        Finset.sum (endpointFiber words start finish i j) fun _ => w := by
    apply Finset.sum_congr rfl
    intro u hu
    exact hconst u hu
  rw [hsum, Finset.sum_const, nsmul_eq_mul]

/-- Paper seed for the endpoint mass matrix bridge.
    prop:parry-endpoint-mass-matrix -/
theorem paper_parry_endpoint_mass_matrix_seeds [DecidableEq α] [DecidableEq ι]
    (words : Finset α) (start finish : α → ι) (pm : α → ℚ)
    (fiberCard : ι → ι → ℕ) (endpointWeight : ι → ι → ℚ)
    (ell r stationary : ι → ℚ)
    (normalizer decay : ℚ) (i j : ι)
    (hcard : (endpointFiber words start finish i j).card = fiberCard i j)
    (hconst : ∀ u ∈ endpointFiber words start finish i j, pm u = endpointWeight i j)
    (hweight : endpointWeight i j = (ell i * r j / normalizer) * decay)
    (hstationary : stationary i = ell i * r i / normalizer)
    (hr_nonzero : r i ≠ 0) :
    endpointMass words start finish pm i j =
        (fiberCard i j : ℚ) * ((ell i * r j / normalizer) * decay) ∧
      endpointMass words start finish pm i j =
        (fiberCard i j : ℚ) * (stationary i * (r j / r i) * decay) := by
  have hmass :=
    endpointMass_eq_card_mul_of_const words start finish pm i j (endpointWeight i j) hconst
  rw [hcard, hweight] at hmass
  constructor
  · exact hmass
  · rw [hmass, hstationary]
    field_simp [hr_nonzero]

/-- Packaged form of the endpoint mass matrix bridge.
    prop:parry-endpoint-mass-matrix -/
theorem paper_parry_endpoint_mass_matrix_package [DecidableEq α] [DecidableEq ι]
    (words : Finset α) (start finish : α → ι) (pm : α → ℚ)
    (fiberCard : ι → ι → ℕ) (endpointWeight : ι → ι → ℚ)
    (ell r stationary : ι → ℚ)
    (normalizer decay : ℚ) (i j : ι)
    (hcard : (endpointFiber words start finish i j).card = fiberCard i j)
    (hconst : ∀ u ∈ endpointFiber words start finish i j, pm u = endpointWeight i j)
    (hweight : endpointWeight i j = (ell i * r j / normalizer) * decay)
    (hstationary : stationary i = ell i * r i / normalizer)
    (hr_nonzero : r i ≠ 0) :
    endpointMass words start finish pm i j =
        (fiberCard i j : ℚ) * ((ell i * r j / normalizer) * decay) ∧
      endpointMass words start finish pm i j =
        (fiberCard i j : ℚ) * (stationary i * (r j / r i) * decay) :=
  paper_parry_endpoint_mass_matrix_seeds words start finish pm fiberCard endpointWeight ell r
    stationary normalizer decay i j hcard hconst hweight hstationary hr_nonzero

end Omega.GU.ParryEndpointMassMatrix
