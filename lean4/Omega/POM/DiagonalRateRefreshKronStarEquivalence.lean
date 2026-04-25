import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

namespace Omega.POM

open scoped BigOperators

/-- The normalizing scalar `S_δ = ∑_z π_δ(z) / r_δ(z)`. -/
def pom_diagonal_rate_refresh_kron_star_equivalence_normalizer {α : Type*} [Fintype α]
    (r π : α → ℚ) : ℚ :=
  ∑ z, π z / r z

/-- Off-diagonal conductance `c_xy = w(x) r_δ(x) π_δ(y)` written in the rank-one refresh
coordinates. -/
def pom_diagonal_rate_refresh_kron_star_equivalence_conductance {α : Type*}
    (w r π : α → ℚ) (x y : α) : ℚ :=
  w x * r x * π y

/-- Leaf conductance of the star network whose Kron reduction matches the rank-one conductance. -/
def pom_diagonal_rate_refresh_kron_star_equivalence_starLeaf {α : Type*} [Fintype α]
    (r π : α → ℚ) (x : α) : ℚ :=
  π x / pom_diagonal_rate_refresh_kron_star_equivalence_normalizer r π

/-- Leaf-to-leaf conductance produced by the Schur-complement formula for the star graph. -/
def pom_diagonal_rate_refresh_kron_star_equivalence_kronConductance {α : Type*} [Fintype α]
    (r π : α → ℚ) (x y : α) : ℚ :=
  pom_diagonal_rate_refresh_kron_star_equivalence_starLeaf r π x *
      pom_diagonal_rate_refresh_kron_star_equivalence_starLeaf r π y /
    ∑ z, pom_diagonal_rate_refresh_kron_star_equivalence_starLeaf r π z

/-- Paper label: `prop:pom-diagonal-rate-refresh-kron-star-equivalence`.
Detailed balance makes `w(x) r_δ(x)` proportional to `π_δ(x)`; summing determines the constant
`S_δ⁻¹`, and the resulting rank-one conductance is exactly the Kron reduction of the corresponding
star network. -/
theorem paper_pom_diagonal_rate_refresh_kron_star_equivalence
    {α : Type*} [Fintype α] [DecidableEq α]
    (w r π : α → ℚ) (x0 : α) (hpi0 : π x0 ≠ 0)
    (hbalance : ∀ x y, w x * r x * π y = w y * r y * π x)
    (hwsum : ∑ x, w x = 1) (hr : ∀ x, r x ≠ 0) (hpi : ∑ x, π x = 1) :
    (∀ x, w x * r x = (w x0 * r x0 / π x0) * π x) ∧
      w x0 * r x0 / π x0 =
        1 / pom_diagonal_rate_refresh_kron_star_equivalence_normalizer r π ∧
      (∀ x y,
        pom_diagonal_rate_refresh_kron_star_equivalence_conductance w r π x y =
          π x * π y / pom_diagonal_rate_refresh_kron_star_equivalence_normalizer r π) ∧
      (∀ x,
        pom_diagonal_rate_refresh_kron_star_equivalence_starLeaf r π x =
          π x / pom_diagonal_rate_refresh_kron_star_equivalence_normalizer r π) ∧
      (∀ x y,
        pom_diagonal_rate_refresh_kron_star_equivalence_kronConductance r π x y =
          π x * π y / pom_diagonal_rate_refresh_kron_star_equivalence_normalizer r π) := by
  let C : ℚ := w x0 * r x0 / π x0
  let S : ℚ := pom_diagonal_rate_refresh_kron_star_equivalence_normalizer r π
  have hprop : ∀ x, w x * r x = C * π x := by
    intro x
    dsimp [C]
    field_simp [hpi0]
    simpa [C, mul_assoc, mul_left_comm, mul_comm] using hbalance x x0
  have hw : ∀ x, w x = C * (π x / r x) := by
    intro x
    field_simp [hr x]
    simpa [mul_assoc, mul_left_comm, mul_comm] using hprop x
  have hsum_CS : (∑ z, w z) = C * S := by
    calc
      ∑ z, w z = ∑ z, C * (π z / r z) := by
        simp [hw]
      _ = C * ∑ z, π z / r z := by
        rw [Finset.mul_sum]
      _ = C * S := by rfl
  have hCS : C * S = 1 := by
    rw [hsum_CS] at hwsum
    exact hwsum
  have hS_nonzero : S ≠ 0 := by
    intro hS
    simp [hS] at hCS
  have hC : C = 1 / S := by
    exact (eq_div_iff hS_nonzero).2 hCS
  have hconductance :
      ∀ x y,
        pom_diagonal_rate_refresh_kron_star_equivalence_conductance w r π x y =
          π x * π y / S := by
    intro x y
    unfold pom_diagonal_rate_refresh_kron_star_equivalence_conductance
    rw [hprop x, hC]
    field_simp [hS_nonzero]
  have hleaf :
      ∀ x, pom_diagonal_rate_refresh_kron_star_equivalence_starLeaf r π x = π x / S := by
    intro x
    rfl
  have hstar_sum :
      (∑ z, pom_diagonal_rate_refresh_kron_star_equivalence_starLeaf r π z) = 1 / S := by
    calc
      ∑ z, pom_diagonal_rate_refresh_kron_star_equivalence_starLeaf r π z
          = ∑ z, π z / S := by
              simp [pom_diagonal_rate_refresh_kron_star_equivalence_starLeaf, S]
      _ = (∑ z, π z) / S := by
            simp [div_eq_mul_inv, Finset.sum_mul]
      _ = 1 / S := by rw [hpi]
  have hkron :
      ∀ x y,
        pom_diagonal_rate_refresh_kron_star_equivalence_kronConductance r π x y =
          π x * π y / S := by
    intro x y
    rw [pom_diagonal_rate_refresh_kron_star_equivalence_kronConductance, hstar_sum]
    simp [pom_diagonal_rate_refresh_kron_star_equivalence_starLeaf, S]
    field_simp [hS_nonzero]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [C] using hprop
  · simpa [C, S] using hC
  · simpa [S] using hconductance
  · simpa [S] using hleaf
  · simpa [S] using hkron

end Omega.POM
