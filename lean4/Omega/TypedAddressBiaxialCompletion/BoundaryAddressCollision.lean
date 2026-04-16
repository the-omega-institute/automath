import Mathlib.Tactic

namespace Omega.TypedAddressBiaxialCompletion.BoundaryAddressCollision

open Finset
open scoped BigOperators

set_option maxHeartbeats 400000 in
/-- Finite-address averaging wrapper: if the total occupancy across `2^b` dyadic addresses is at
    least `c T^2 log T`, then one address class carries at least the average occupancy.
    prop:typed-address-biaxial-completion-boundary-address-collision -/
theorem paper_typed_address_biaxial_completion_boundary_address_collision
    (c T : ℝ) (b : ℕ) (addressOccupancy : Fin (2 ^ b) → ℝ)
    (hNonneg : ∀ a, 0 ≤ addressOccupancy a)
    (hTotal : c * T^2 * Real.log T ≤ ∑ a, addressOccupancy a) :
    ∃ a : Fin (2 ^ b), c * T^2 * Real.log T / (2 : ℝ) ^ b ≤ addressOccupancy a := by
  classical
  obtain ⟨a, ha, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (Fin (2 ^ b))) addressOccupancy Finset.univ_nonempty
  refine ⟨a, ?_⟩
  have hsum_le : (∑ x : Fin (2 ^ b), addressOccupancy x) ≤ ∑ _x : Fin (2 ^ b), addressOccupancy a := by
    refine Finset.sum_le_sum ?_
    intro x hx
    exact hmax x (by simp)
  have hpow_cast : (((2 ^ b : ℕ)) : ℝ) = (2 : ℝ) ^ b := by
    norm_num
  have hmajor :
      c * T^2 * Real.log T ≤ ((2 : ℝ) ^ b) * addressOccupancy a := by
    calc
      c * T^2 * Real.log T ≤ ∑ x : Fin (2 ^ b), addressOccupancy x := hTotal
      _ ≤ ∑ _x : Fin (2 ^ b), addressOccupancy a := hsum_le
      _ = (((2 ^ b : ℕ)) : ℝ) * addressOccupancy a := by simp
      _ = (2 : ℝ) ^ b * addressOccupancy a := by rw [hpow_cast]
  have hpow_pos : 0 < (2 : ℝ) ^ b := by positivity
  exact (div_le_iff₀ hpow_pos).2 (by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmajor)

end Omega.TypedAddressBiaxialCompletion.BoundaryAddressCollision
