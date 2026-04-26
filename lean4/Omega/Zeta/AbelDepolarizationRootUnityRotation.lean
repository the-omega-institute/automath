import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Omega.Zeta.AbelPowerbaseCovariancePolePowerMap

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/-- The geometric sum `S_m(u) = 1 + u + ··· + u^(m-1)` controlling the depolarized denominator. -/
def abel_depolarization_root_unity_rotation_geometric_sum (m : ℕ) (u : ℂ) : ℂ :=
  Finset.sum (Finset.range m) fun j => u ^ j

/-- The depolarization kernel `K_m(u) = (1 - u)⁻¹ - m / (1 - u^m)`. -/
def abel_depolarization_root_unity_rotation_kernel (m : ℕ) (u : ℂ) : ℂ :=
  (1 - u)⁻¹ - (m : ℂ) * (1 - u ^ m)⁻¹

/-- A regularized extension of `K_m` at `u = 1`, using the explicit removable value. -/
def abel_depolarization_root_unity_rotation_regularized_kernel (m : ℕ) (u : ℂ) : ℂ :=
  if u = 1 then -((m - 1 : ℂ) / 2) else abel_depolarization_root_unity_rotation_kernel m u

private lemma abel_depolarization_root_unity_rotation_geom_sum_mul
    (m : ℕ) (u : ℂ) :
    abel_depolarization_root_unity_rotation_geometric_sum m u * (u - 1) = u ^ m - 1 := by
  simpa [abel_depolarization_root_unity_rotation_geometric_sum] using geom_sum_mul u m

private lemma abel_depolarization_root_unity_rotation_geom_sum_mul_neg
    (m : ℕ) (u : ℂ) :
    abel_depolarization_root_unity_rotation_geometric_sum m u * (1 - u) = 1 - u ^ m := by
  simpa [abel_depolarization_root_unity_rotation_geometric_sum] using geom_sum_mul_neg u m

private lemma abel_depolarization_root_unity_rotation_geometric_sum_eq_zero_iff
    (m : ℕ) {u : ℂ} (hu : u ≠ 1) :
    abel_depolarization_root_unity_rotation_geometric_sum m u = 0 ↔ u ^ m = 1 := by
  constructor
  · intro hsum
    have hprod :=
      abel_depolarization_root_unity_rotation_geom_sum_mul m u
    rw [hsum, zero_mul] at hprod
    exact sub_eq_zero.mp (by simpa using hprod.symm)
  · intro hum
    have hprod :=
      abel_depolarization_root_unity_rotation_geom_sum_mul m u
    have hzero : abel_depolarization_root_unity_rotation_geometric_sum m u * (u - 1) = 0 := by
      rw [hprod, hum, sub_self]
    have hu' : u - 1 ≠ 0 := sub_ne_zero.mpr hu
    exact (mul_eq_zero.mp hzero).resolve_right hu'

/-- Paper label: `thm:abel-depolarization-root-unity-rotation`. The powerbase covariance package
rewrites the `b^m` data in terms of the base-`b` data, the depolarization kernel admits the
geometric-sum denominator factorization, the nontrivial possible poles are exactly detected by
`u^m = 1` with `u ≠ 1`, and the regularized value at `u = 1` is `-(m - 1) / 2`. -/
theorem paper_abel_depolarization_root_unity_rotation
    (ψ h : ℕ → ℕ) (b m ρ δ : ℕ) :
    xiAbelCoeff ψ (b ^ m) = xiAbelDecimation m (xiAbelCoeff ψ b) ∧
      xiAbelDampedSeries ψ (b ^ m) δ = xiAbelDecimation m (xiAbelDampedSeries ψ b δ) ∧
      xiAbelAnalyticRemainder h (b ^ m) δ =
        xiAbelDecimation m (xiAbelAnalyticRemainder h b δ) ∧
      xiAbelPoleMap (b ^ m) ρ δ = (xiAbelPoleMap b ρ δ) ^ m ∧
      (∀ u : ℂ,
        1 - u ^ m =
          (1 - u) * abel_depolarization_root_unity_rotation_geometric_sum m u) ∧
      (∀ {u : ℂ}, u ≠ 1 →
        (abel_depolarization_root_unity_rotation_geometric_sum m u = 0 ↔ u ^ m = 1)) ∧
      abel_depolarization_root_unity_rotation_regularized_kernel m 1 = -((m - 1 : ℂ) / 2) := by
  rcases paper_xi_abel_powerbase_covariance_pole_power_map ψ h b m ρ δ with
    ⟨hCoeff, hDamped, hRem, hPole⟩
  refine ⟨hCoeff, hDamped, hRem, hPole, ?_, ?_, ?_⟩
  · intro u
    simpa [mul_comm] using (abel_depolarization_root_unity_rotation_geom_sum_mul_neg m u).symm
  · intro u
    exact abel_depolarization_root_unity_rotation_geometric_sum_eq_zero_iff (m := m) (u := u)
  · simp [abel_depolarization_root_unity_rotation_regularized_kernel]

end

end Omega.Zeta
