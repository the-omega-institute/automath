import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

open scoped BigOperators

/-- Finite atomic Stieltjes data for the log-potential integral package. -/
structure xi_logpotential_integral_geomean_data where
  κ : ℕ
  a : Fin κ → ℝ
  w : Fin κ → ℝ

/-- Total mass `Φ = Σ wⱼ`. -/
def xi_logpotential_integral_geomean_total_mass
    (D : xi_logpotential_integral_geomean_data) : ℝ :=
  ∑ j : Fin D.κ, D.w j

/-- Atomic Stieltjes sum `S(t) = Σ wⱼ / (t + aⱼ)`. -/
def xi_logpotential_integral_geomean_stieltjes_sum
    (D : xi_logpotential_integral_geomean_data) (t : ℝ) : ℝ :=
  ∑ j : Fin D.κ, D.w j / (t + D.a j)

/-- The reference orbit `Φ / (t + 1)`. -/
def xi_logpotential_integral_geomean_reference_orbit
    (D : xi_logpotential_integral_geomean_data) (t : ℝ) : ℝ :=
  xi_logpotential_integral_geomean_total_mass D / (t + 1)

/-- Termwise rewrite of `S(t) - Φ / (t + 1)`. -/
def xi_logpotential_integral_geomean_termwise_rewrite
    (D : xi_logpotential_integral_geomean_data) (t : ℝ) : ℝ :=
  ∑ j : Fin D.κ, D.w j * ((1 / (t + D.a j)) - (1 / (t + 1)))

/-- Weighted logarithmic sum appearing in the geometric mean formula. -/
def xi_logpotential_integral_geomean_weighted_logs
    (D : xi_logpotential_integral_geomean_data) : ℝ :=
  ∑ j : Fin D.κ, D.w j * Real.log (D.a j)

/-- The finite Stieltjes rewrite together with the weighted-log collapse. -/
def xi_logpotential_integral_geomean_statement
    (D : xi_logpotential_integral_geomean_data) : Prop :=
  (∀ t,
      xi_logpotential_integral_geomean_stieltjes_sum D t -
          xi_logpotential_integral_geomean_reference_orbit D t =
        xi_logpotential_integral_geomean_termwise_rewrite D t) ∧
    (-xi_logpotential_integral_geomean_weighted_logs D =
      ∑ j : Fin D.κ, D.w j * (-Real.log (D.a j)))

/-- Paper label: `prop:xi-logpotential-integral-geomean`. -/
theorem paper_xi_logpotential_integral_geomean
    (D : xi_logpotential_integral_geomean_data) :
    xi_logpotential_integral_geomean_statement D := by
  refine ⟨?_, ?_⟩
  · intro t
    unfold xi_logpotential_integral_geomean_stieltjes_sum
      xi_logpotential_integral_geomean_reference_orbit
      xi_logpotential_integral_geomean_termwise_rewrite
      xi_logpotential_integral_geomean_total_mass
    calc
      (∑ j : Fin D.κ, D.w j / (t + D.a j)) - (∑ j : Fin D.κ, D.w j) / (t + 1) =
          (∑ j : Fin D.κ, D.w j / (t + D.a j)) - ∑ j : Fin D.κ, D.w j / (t + 1) := by
            rw [← Finset.sum_div]
      _ = ∑ j : Fin D.κ, (D.w j / (t + D.a j) - D.w j / (t + 1)) := by
            rw [Finset.sum_sub_distrib]
      _ = ∑ j : Fin D.κ, D.w j * ((1 / (t + D.a j)) - (1 / (t + 1))) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            simp [div_eq_mul_inv, sub_eq_add_neg, mul_add, mul_neg]
  · calc
      -xi_logpotential_integral_geomean_weighted_logs D =
          ∑ j : Fin D.κ, -(D.w j * Real.log (D.a j)) := by
            simp [xi_logpotential_integral_geomean_weighted_logs]
      _ = ∑ j : Fin D.κ, D.w j * (-Real.log (D.a j)) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            ring

end

end Omega.Zeta
