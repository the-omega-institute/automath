import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- Total complement mass in the audited window. -/
noncomputable def xi_foldbin_audited_even_minsector_collision_explicit_floor_complementMass
    {k : ℕ} (complementFiber : Fin k → ℝ) : ℝ :=
  ∑ i, complementFiber i

/-- Exact collision identity split into the minimal sector and its complement. -/
noncomputable def xi_foldbin_audited_even_minsector_collision_explicit_floor_collision
    {k : ℕ} (minSectorMass : ℝ) (complementFiber : Fin k → ℝ) (ambientMass : ℝ) : ℝ :=
  (minSectorMass ^ 2 + ∑ i, complementFiber i ^ 2) / ambientMass ^ 2

/-- Explicit Cauchy-Schwarz floor for the collision term. -/
noncomputable def xi_foldbin_audited_even_minsector_collision_explicit_floor_collisionFloor
    {k : ℕ} (minSectorMass : ℝ) (complementFiber : Fin k → ℝ) (ambientMass : ℝ) : ℝ :=
  (minSectorMass ^ 2 +
      xi_foldbin_audited_even_minsector_collision_explicit_floor_complementMass complementFiber ^ 2 /
        (k : ℝ)) /
    ambientMass ^ 2

/-- The chi-square value obtained from the collision identity. -/
noncomputable def xi_foldbin_audited_even_minsector_collision_explicit_floor_chi2
    {k : ℕ} (sectorCount minSectorMass : ℝ) (complementFiber : Fin k → ℝ)
    (ambientMass : ℝ) : ℝ :=
  sectorCount *
      xi_foldbin_audited_even_minsector_collision_explicit_floor_collision minSectorMass
        complementFiber ambientMass -
    1

/-- Explicit chi-square floor corresponding to the collision floor. -/
noncomputable def xi_foldbin_audited_even_minsector_collision_explicit_floor_chi2Floor
    {k : ℕ} (sectorCount minSectorMass : ℝ) (complementFiber : Fin k → ℝ)
    (ambientMass : ℝ) : ℝ :=
  sectorCount *
      xi_foldbin_audited_even_minsector_collision_explicit_floor_collisionFloor minSectorMass
        complementFiber ambientMass -
    1

/-- Uniformity of the complement fibers, the Cauchy-Schwarz equality case. -/
def xi_foldbin_audited_even_minsector_collision_explicit_floor_uniformComplement
    {k : ℕ} (complementFiber : Fin k → ℝ) : Prop :=
  ∀ i,
    complementFiber i =
      xi_foldbin_audited_even_minsector_collision_explicit_floor_complementMass complementFiber /
        (k : ℝ)

private lemma xi_foldbin_audited_even_minsector_collision_explicit_floor_complement_cauchy
    {k : ℕ} (hk : 0 < k) (complementFiber : Fin k → ℝ) :
    xi_foldbin_audited_even_minsector_collision_explicit_floor_complementMass complementFiber ^ 2 /
        (k : ℝ) ≤
      ∑ i, complementFiber i ^ 2 := by
  have hcard_pos : (0 : ℝ) < (k : ℝ) := by
    exact_mod_cast hk
  have hcs :
      (∑ i, complementFiber i) ^ 2 ≤ (k : ℝ) * ∑ i, complementFiber i ^ 2 := by
    simpa [Fintype.card_fin] using
      (sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin k)))
        (f := complementFiber))
  rw [xi_foldbin_audited_even_minsector_collision_explicit_floor_complementMass]
  exact (div_le_iff₀ hcard_pos).2 (by simpa [mul_comm] using hcs)

/-- Paper label: `thm:xi-foldbin-audited-even-minsector-collision-explicit-floor`. -/
theorem paper_xi_foldbin_audited_even_minsector_collision_explicit_floor
    {k : ℕ} (hk : 0 < k) (minSectorMass : ℝ) (complementFiber : Fin k → ℝ)
    (ambientMass : ℝ) (hambientMass : 0 < ambientMass) (sectorCount : ℝ)
    (hsectorCount : 0 ≤ sectorCount)
    (hcauchyEquality :
      xi_foldbin_audited_even_minsector_collision_explicit_floor_collision minSectorMass
            complementFiber ambientMass =
          xi_foldbin_audited_even_minsector_collision_explicit_floor_collisionFloor minSectorMass
            complementFiber ambientMass ↔
        xi_foldbin_audited_even_minsector_collision_explicit_floor_uniformComplement
          complementFiber) :
    xi_foldbin_audited_even_minsector_collision_explicit_floor_collisionFloor minSectorMass
          complementFiber ambientMass ≤
        xi_foldbin_audited_even_minsector_collision_explicit_floor_collision minSectorMass
          complementFiber ambientMass ∧
      xi_foldbin_audited_even_minsector_collision_explicit_floor_chi2Floor sectorCount
            minSectorMass complementFiber ambientMass ≤
          xi_foldbin_audited_even_minsector_collision_explicit_floor_chi2 sectorCount
            minSectorMass complementFiber ambientMass ∧
        (xi_foldbin_audited_even_minsector_collision_explicit_floor_collision minSectorMass
              complementFiber ambientMass =
            xi_foldbin_audited_even_minsector_collision_explicit_floor_collisionFloor minSectorMass
              complementFiber ambientMass ↔
          xi_foldbin_audited_even_minsector_collision_explicit_floor_uniformComplement
            complementFiber) := by
  have hcollision :
      xi_foldbin_audited_even_minsector_collision_explicit_floor_collisionFloor minSectorMass
          complementFiber ambientMass ≤
        xi_foldbin_audited_even_minsector_collision_explicit_floor_collision minSectorMass
          complementFiber ambientMass := by
    dsimp
      [xi_foldbin_audited_even_minsector_collision_explicit_floor_collisionFloor,
        xi_foldbin_audited_even_minsector_collision_explicit_floor_collision]
    gcongr
    exact xi_foldbin_audited_even_minsector_collision_explicit_floor_complement_cauchy hk
      complementFiber
  have hchi2 :
      xi_foldbin_audited_even_minsector_collision_explicit_floor_chi2Floor sectorCount
            minSectorMass complementFiber ambientMass ≤
          xi_foldbin_audited_even_minsector_collision_explicit_floor_chi2 sectorCount
            minSectorMass complementFiber ambientMass := by
    dsimp
      [xi_foldbin_audited_even_minsector_collision_explicit_floor_chi2,
        xi_foldbin_audited_even_minsector_collision_explicit_floor_chi2Floor]
    exact sub_le_sub_right (mul_le_mul_of_nonneg_left hcollision hsectorCount) 1
  exact ⟨hcollision, hchi2, hcauchyEquality⟩

end Omega.Zeta
