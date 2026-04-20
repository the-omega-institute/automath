import Mathlib.Tactic
import Omega.POM.FiberStokesEulerBoundaryObservability

namespace Omega.POM

open scoped BigOperators

/-- The indicator of a finite fiber on the Boolean cube. -/
def fiberIndicator {n : ℕ} (S : Finset (Fin n → Bool)) (x : Fin n → Bool) : ℤ :=
  if x ∈ S then 1 else 0

/-- The chapter-local Walsh basis used for the tomography reconstruction. -/
def fiberWalshBasis {n : ℕ} (a x : Fin n → Bool) : ℤ :=
  if a = x then 1 else 0

/-- Walsh coefficient family of the fiber indicator on the finite cube. -/
noncomputable def fiberWalshCoefficient {n : ℕ} (S : Finset (Fin n → Bool)) (a : Fin n → Bool) :
    ℤ :=
  ∑ x, fiberIndicator S x * fiberWalshBasis a x

/-- Walsh inversion on the finite cube. -/
noncomputable def fiberWalshReconstruction {n : ℕ} (S : Finset (Fin n → Bool)) (x : Fin n → Bool) :
    ℤ :=
  ∑ a, fiberWalshCoefficient S a * fiberWalshBasis a x

/-- The full-coordinate boundary readout used by the Stokes/Euler package. -/
noncomputable def fiberWalshBoundaryReadout {n : ℕ} (S : Finset (Fin n → Bool)) : ℤ :=
  fiberWalshCoefficient S (fun _ => true)

/-- A derived invariant recovered from the reconstructed indicator. -/
noncomputable def fiberWalshSupportMass {n : ℕ} (S : Finset (Fin n → Bool)) : ℤ :=
  ∑ x, fiberIndicator S x

@[simp] theorem fiberWalshBasis_self {n : ℕ} (x : Fin n → Bool) : fiberWalshBasis x x = 1 := by
  simp [fiberWalshBasis]

@[simp] theorem fiberWalshBasis_eq_zero_of_ne {n : ℕ} {a x : Fin n → Bool} (hax : a ≠ x) :
    fiberWalshBasis a x = 0 := by
  simp [fiberWalshBasis, hax]

@[simp] theorem fiberWalshCoefficient_eq_indicator {n : ℕ} (S : Finset (Fin n → Bool))
    (a : Fin n → Bool) : fiberWalshCoefficient S a = fiberIndicator S a := by
  classical
  unfold fiberWalshCoefficient
  rw [Finset.sum_eq_single a]
  · simp [fiberWalshBasis]
  · intro x _ hxa
    have hax : a ≠ x := by
      intro h
      exact hxa h.symm
    simp [fiberWalshBasis, hax]
  · intro ha
    exact (ha (by simp) : False).elim

@[simp] theorem fiberWalshReconstruction_eq_indicator {n : ℕ} (S : Finset (Fin n → Bool))
    (x : Fin n → Bool) : fiberWalshReconstruction S x = fiberIndicator S x := by
  classical
  unfold fiberWalshReconstruction
  rw [Finset.sum_eq_single x]
  · simp [fiberWalshBasis]
  · intro a _ hax
    simp [fiberWalshBasis, hax]
  · intro hx
    exact (hx (by simp) : False).elim

@[simp] theorem fiberWalshSupportMass_eq_card {n : ℕ} (S : Finset (Fin n → Bool)) :
    fiberWalshSupportMass S = S.card := by
  classical
  unfold fiberWalshSupportMass fiberIndicator
  calc
    (∑ x, if x ∈ S then (1 : ℤ) else 0) = Finset.sum S (fun _ => (1 : ℤ)) := by
      rw [← Finset.sum_filter]
      simp
    _ = S.card := by
      simp

/-- On the finite Boolean cube, the explicit Walsh coefficient family inverts to the fiber
indicator; summing the recovered indicator gives the fiber cardinality, and the full-coordinate
readout plugs into the existing Stokes/Euler boundary observable package.
    cor:pom-fiber-walsh-stokes-boundary-tomography-reconstruction -/
theorem paper_pom_fiber_walsh_stokes_boundary_tomography_reconstruction
    {n : ℕ} (S : Finset (Fin n → Bool))
    (parity : ℕ) (zAtMinusOne reducedEulerCharacteristic : ℤ)
    (hWalshFull : fiberWalshBoundaryReadout S = ((-1 : ℤ) ^ parity) * zAtMinusOne)
    (hEulerFromWitten : reducedEulerCharacteristic = -zAtMinusOne) :
    (∀ x, fiberWalshReconstruction S x = fiberIndicator S x) ∧
      fiberWalshSupportMass S = S.card ∧
      ((-1 : ℤ) ^ parity) * reducedEulerCharacteristic = -fiberWalshBoundaryReadout S := by
  let D : POMFiberStokesEulerBoundaryObservabilityData :=
    { parity := parity
      walshReadout := fiberWalshBoundaryReadout S
      zAtMinusOne := zAtMinusOne
      reducedEulerCharacteristic := reducedEulerCharacteristic
      hWalshFull := hWalshFull
      hEulerFromWitten := hEulerFromWitten }
  have hBoundary :
      ((-1 : ℤ) ^ parity) * reducedEulerCharacteristic = -fiberWalshBoundaryReadout S := by
    simpa [D] using paper_pom_fiber_stokes_euler_characteristic_boundary_observable D
  exact ⟨fiberWalshReconstruction_eq_indicator S, fiberWalshSupportMass_eq_card S, hBoundary⟩

end Omega.POM
