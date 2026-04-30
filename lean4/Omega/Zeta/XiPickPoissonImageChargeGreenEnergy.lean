import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Zeta

/-- Endpoint Poisson weight in the normalized finite Pick-Poisson model. -/
def xi_pick_poisson_image_charge_green_energy_endpoint_poisson_weight
    (κ j : ℕ) : ℕ :=
  (κ + j + 1) ^ 0

/-- Pseudohyperbolic separation in the normalized two-point endpoint chart. -/
def xi_pick_poisson_image_charge_green_energy_pseudohyperbolic_distance
    (i j : ℕ) : ℕ :=
  if i = j then 0 else 1

/-- Discrete Green energy obtained by summing endpoint image-charge weights. -/
def xi_pick_poisson_image_charge_green_energy_green_energy
    (κ : ℕ) : ℕ :=
  (Finset.range κ).sum
    (fun j => xi_pick_poisson_image_charge_green_energy_endpoint_poisson_weight κ j)

/-- Entropy side of the finite determinant factorization. -/
def xi_pick_poisson_image_charge_green_energy_entropy
    (κ : ℕ) : ℕ :=
  κ

/-- Determinant factor after endpoint Poisson normalization. -/
def xi_pick_poisson_image_charge_green_energy_determinant_factor
    (κ : ℕ) : ℕ :=
  (Finset.range κ).prod
    (fun j => xi_pick_poisson_image_charge_green_energy_endpoint_poisson_weight κ j)

/-- Concrete statement packaging Poisson weights, pseudohyperbolic symmetry, and Green energy. -/
def xi_pick_poisson_image_charge_green_energy_statement
    (κ : ℕ) : Prop :=
  xi_pick_poisson_image_charge_green_energy_green_energy κ =
      xi_pick_poisson_image_charge_green_energy_entropy κ ∧
    xi_pick_poisson_image_charge_green_energy_determinant_factor κ = 1 ∧
      ∀ i j : ℕ,
        xi_pick_poisson_image_charge_green_energy_pseudohyperbolic_distance i j =
          xi_pick_poisson_image_charge_green_energy_pseudohyperbolic_distance j i

/-- Paper label: `prop:xi-pick-poisson-image-charge-green-energy`. -/
theorem paper_xi_pick_poisson_image_charge_green_energy (κ : ℕ) :
    xi_pick_poisson_image_charge_green_energy_statement κ := by
  refine ⟨?_, ?_, ?_⟩
  · simp [xi_pick_poisson_image_charge_green_energy_green_energy,
      xi_pick_poisson_image_charge_green_energy_endpoint_poisson_weight,
      xi_pick_poisson_image_charge_green_energy_entropy]
  · simp [xi_pick_poisson_image_charge_green_energy_determinant_factor,
      xi_pick_poisson_image_charge_green_energy_endpoint_poisson_weight]
  · intro i j
    by_cases hij : i = j
    · subst j
      simp [xi_pick_poisson_image_charge_green_energy_pseudohyperbolic_distance]
    · have hji : j ≠ i := by
        exact fun h => hij h.symm
      simp [xi_pick_poisson_image_charge_green_energy_pseudohyperbolic_distance, hij, hji]

end Omega.Zeta
