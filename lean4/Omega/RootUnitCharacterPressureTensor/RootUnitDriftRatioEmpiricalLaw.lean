import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.RootUnitCharacterPressureTensor

section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The total multiplicity in the finite ellipsoidal truncation model. -/
def root_unit_drift_ratio_empirical_law_total_weight (weight : ι → ℕ) : ℕ :=
  ∑ u, weight u

/-- The finite truncation repeats the direction `u` exactly `N * weight u` times. -/
abbrev root_unit_drift_ratio_empirical_law_ellipsoidal_truncation (weight : ι → ℕ) (N : ℕ) :=
  Σ u : ι, Fin (N * weight u)

/-- The weighted spherical mass attached to the truncation model. -/
def root_unit_drift_ratio_empirical_law_weighted_spherical_mass (weight : ι → ℕ) : ℝ :=
  ∑ u, (weight u : ℝ)

/-- The limiting weighted spherical average of a test function. -/
noncomputable def root_unit_drift_ratio_empirical_law_weighted_spherical_average
    (weight : ι → ℕ) (drift : ι → ℝ) (Φ : ℝ → ℝ) : ℝ :=
  (∑ u, (weight u : ℝ) * Φ (drift u)) /
    root_unit_drift_ratio_empirical_law_weighted_spherical_mass weight

/-- The empirical average on the `N`th truncation. -/
noncomputable def root_unit_drift_ratio_empirical_law_empirical_average
    (weight : ι → ℕ) (drift : ι → ℝ) (Φ : ℝ → ℝ) (N : ℕ) : ℝ :=
  (∑ p : root_unit_drift_ratio_empirical_law_ellipsoidal_truncation weight N, Φ (drift p.1)) /
    (Fintype.card (root_unit_drift_ratio_empirical_law_ellipsoidal_truncation weight N) : ℝ)

omit [DecidableEq ι] in
lemma root_unit_drift_ratio_empirical_law_truncation_card
    (weight : ι → ℕ) (N : ℕ) :
    Fintype.card (root_unit_drift_ratio_empirical_law_ellipsoidal_truncation weight N) =
      N * root_unit_drift_ratio_empirical_law_total_weight weight := by
  rw [Fintype.card_sigma]
  simp [root_unit_drift_ratio_empirical_law_total_weight, Finset.mul_sum]

omit [DecidableEq ι] in
lemma root_unit_drift_ratio_empirical_law_weighted_spherical_volume_formula
    (weight : ι → ℕ) (drift : ι → ℝ) (Φ : ℝ → ℝ) (N : ℕ) :
    (∑ p : root_unit_drift_ratio_empirical_law_ellipsoidal_truncation weight N, Φ (drift p.1)) =
      ∑ u, (N * weight u : ℝ) * Φ (drift u) := by
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    (Fintype.sum_sigma' (f := fun u (_ : Fin (N * weight u)) => Φ (drift u)))

omit [DecidableEq ι] in
lemma root_unit_drift_ratio_empirical_law_weighted_sum_factorization
    (weight : ι → ℕ) (drift : ι → ℝ) (Φ : ℝ → ℝ) (N : ℕ) :
    (∑ u, (N * weight u : ℝ) * Φ (drift u)) =
      (N : ℝ) * ∑ u, (weight u : ℝ) * Φ (drift u) := by
  simp [Finset.mul_sum, mul_left_comm, mul_comm]

omit [DecidableEq ι] in
lemma root_unit_drift_ratio_empirical_law_weighted_mass_factorization
    (weight : ι → ℕ) (N : ℕ) :
    (Fintype.card (root_unit_drift_ratio_empirical_law_ellipsoidal_truncation weight N) : ℝ) =
      (N : ℝ) * root_unit_drift_ratio_empirical_law_weighted_spherical_mass weight := by
  rw [root_unit_drift_ratio_empirical_law_truncation_card]
  simp [root_unit_drift_ratio_empirical_law_weighted_spherical_mass,
    root_unit_drift_ratio_empirical_law_total_weight, Nat.cast_mul]

/-- Paper label: `thm:root-unit-drift-ratio-empirical-law`.
In the finite weighted truncation model, the lattice count is linear in the truncation parameter,
the weighted spherical volume formula is exact, and the empirical average is already equal to the
weighted spherical average for every positive truncation level. -/
theorem paper_root_unit_drift_ratio_empirical_law
    (weight : ι → ℕ) (drift : ι → ℝ)
    (hweight : 0 < root_unit_drift_ratio_empirical_law_total_weight weight) (Φ : ℝ → ℝ) :
    (∀ N,
      Fintype.card (root_unit_drift_ratio_empirical_law_ellipsoidal_truncation weight N) =
        N * root_unit_drift_ratio_empirical_law_total_weight weight) ∧
      (∀ N,
        (∑ p : root_unit_drift_ratio_empirical_law_ellipsoidal_truncation weight N,
            Φ (drift p.1)) =
          ∑ u, (N * weight u : ℝ) * Φ (drift u)) ∧
      ∀ N, 0 < N →
        root_unit_drift_ratio_empirical_law_empirical_average weight drift Φ N =
          root_unit_drift_ratio_empirical_law_weighted_spherical_average weight drift Φ := by
  refine ⟨root_unit_drift_ratio_empirical_law_truncation_card weight,
    root_unit_drift_ratio_empirical_law_weighted_spherical_volume_formula weight drift Φ, ?_⟩
  intro N hN
  unfold root_unit_drift_ratio_empirical_law_empirical_average
    root_unit_drift_ratio_empirical_law_weighted_spherical_average
  rw [root_unit_drift_ratio_empirical_law_weighted_spherical_volume_formula,
    root_unit_drift_ratio_empirical_law_weighted_sum_factorization,
    root_unit_drift_ratio_empirical_law_weighted_mass_factorization]
  have hN0 : (N : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hN)
  have hW0 : root_unit_drift_ratio_empirical_law_weighted_spherical_mass weight ≠ 0 := by
    have hmass :
        root_unit_drift_ratio_empirical_law_weighted_spherical_mass weight =
          (root_unit_drift_ratio_empirical_law_total_weight weight : ℝ) := by
      simp [root_unit_drift_ratio_empirical_law_weighted_spherical_mass,
        root_unit_drift_ratio_empirical_law_total_weight]
    rw [hmass]
    exact_mod_cast (Nat.ne_of_gt hweight)
  field_simp [hN0, hW0]

end

end Omega.RootUnitCharacterPressureTensor
