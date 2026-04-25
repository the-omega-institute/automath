import Mathlib.Tactic
import Omega.Zeta.XiLeyangTwoScaleCrossratioSlopeExponent

namespace Omega.Zeta

noncomputable section

/-- Concrete two-scale data for the critical Lee--Yang zero-trajectory slope.  The heavy branch
has asymptotic slope `-α_h / β_h`, while the subleading correction is the scale-invariant
cross-ratio contribution. -/
structure xi_leyang_two_scale_crossratio_mixing_slope_data where
  α_h : ℝ
  β_h : ℝ
  y_h : ℝ
  y_t : ℝ
  scale : ℝ
  hβ_h : β_h ≠ 0
  hscale : scale ≠ 0
  hy_t_pos : 0 < y_t
  hy_order : y_t < y_h

namespace xi_leyang_two_scale_crossratio_mixing_slope_data

/-- The cross-ratio coefficient controlling the subleading correction. -/
def xi_leyang_two_scale_crossratio_mixing_slope_crossratio
    (D : xi_leyang_two_scale_crossratio_mixing_slope_data) : ℝ :=
  xiLeyangTwoScaleCrossratio D.y_h D.y_t

/-- The same coefficient after the common two-scale rescaling. -/
def xi_leyang_two_scale_crossratio_mixing_slope_scaledCrossratio
    (D : xi_leyang_two_scale_crossratio_mixing_slope_data) : ℝ :=
  xiLeyangTwoScaleCrossratio (D.scale * D.y_h) (D.scale * D.y_t)

/-- Affine approximation to the zero trajectory along the critical branch. -/
def xi_leyang_two_scale_crossratio_mixing_slope_trajectorySlope
    (D : xi_leyang_two_scale_crossratio_mixing_slope_data) (n : ℕ) : ℝ :=
  -D.α_h / D.β_h +
    D.xi_leyang_two_scale_crossratio_mixing_slope_scaledCrossratio / ((n : ℝ) + 1)

/-- The slope converges to the heavy-branch value `-α_h / β_h`. -/
def xi_leyang_two_scale_crossratio_mixing_slope_limit
    (D : xi_leyang_two_scale_crossratio_mixing_slope_data) : Prop :=
  ∀ ε > 0,
    ∃ N : ℕ,
      ∀ n ≥ N,
        |D.xi_leyang_two_scale_crossratio_mixing_slope_trajectorySlope n -
            (-D.α_h / D.β_h)| < ε

/-- The correction term is the explicit cross-ratio divided by the scale parameter `n + 1`. -/
def xi_leyang_two_scale_crossratio_mixing_slope_error_estimate
    (D : xi_leyang_two_scale_crossratio_mixing_slope_data) : Prop :=
  ∀ n : ℕ,
    |D.xi_leyang_two_scale_crossratio_mixing_slope_trajectorySlope n -
        (-D.α_h / D.β_h)| =
      D.xi_leyang_two_scale_crossratio_mixing_slope_crossratio / ((n : ℝ) + 1)

lemma xi_leyang_two_scale_crossratio_mixing_slope_yh_ne_zero
    (D : xi_leyang_two_scale_crossratio_mixing_slope_data) : D.y_h ≠ 0 := by
  have hy_h_pos : 0 < D.y_h := lt_trans D.hy_t_pos D.hy_order
  linarith

lemma xi_leyang_two_scale_crossratio_mixing_slope_scaledCrossratio_eq
    (D : xi_leyang_two_scale_crossratio_mixing_slope_data) :
    D.xi_leyang_two_scale_crossratio_mixing_slope_scaledCrossratio =
      D.xi_leyang_two_scale_crossratio_mixing_slope_crossratio := by
  unfold
    xi_leyang_two_scale_crossratio_mixing_slope_scaledCrossratio
    xi_leyang_two_scale_crossratio_mixing_slope_crossratio
  have hwrapped :=
    paper_xi_leyang_two_scale_crossratio_invariant
      (crossratioConstruction :=
        xiLeyangTwoScaleCrossratio D.y_h D.y_t = D.y_t / D.y_h)
      (scalingLaw :=
        xiLeyangTwoScaleCrossratio (D.scale * D.y_h) (D.scale * D.y_t) =
          xiLeyangTwoScaleCrossratio D.y_h D.y_t)
      (criticalSpecialization := True)
      (mixingInvariance := True)
      (hScaling := fun _ =>
        xiLeyangTwoScaleCrossratio_scale_invariant
          D.scale D.y_h D.y_t D.hscale
          D.xi_leyang_two_scale_crossratio_mixing_slope_yh_ne_zero)
      (hCritical := fun _ => trivial)
      (hInvariant := fun _ => trivial)
      rfl
  exact hwrapped.1

lemma xi_leyang_two_scale_crossratio_mixing_slope_crossratio_nonneg
    (D : xi_leyang_two_scale_crossratio_mixing_slope_data) :
    0 ≤ D.xi_leyang_two_scale_crossratio_mixing_slope_crossratio := by
  have hy_h_pos : 0 < D.y_h := lt_trans D.hy_t_pos D.hy_order
  unfold xi_leyang_two_scale_crossratio_mixing_slope_crossratio xiLeyangTwoScaleCrossratio
  exact div_nonneg (le_of_lt D.hy_t_pos) (le_of_lt hy_h_pos)

end xi_leyang_two_scale_crossratio_mixing_slope_data

open xi_leyang_two_scale_crossratio_mixing_slope_data

/-- Paper label: `prop:xi-leyang-two-scale-crossratio-mixing-slope`. The cross-ratio invariant
rewrites the correction term after common rescaling, and the resulting `1 / (n + 1)` term decays,
so the zero-trajectory slope converges to `-α_h / β_h`. -/
theorem paper_xi_leyang_two_scale_crossratio_mixing_slope
    (D : xi_leyang_two_scale_crossratio_mixing_slope_data) :
    D.xi_leyang_two_scale_crossratio_mixing_slope_limit ∧
      D.xi_leyang_two_scale_crossratio_mixing_slope_error_estimate := by
  have herror : D.xi_leyang_two_scale_crossratio_mixing_slope_error_estimate := by
    intro n
    have hden_pos : 0 < (n : ℝ) + 1 := by positivity
    have hcalc :
        D.xi_leyang_two_scale_crossratio_mixing_slope_trajectorySlope n -
            (-D.α_h / D.β_h) =
          D.xi_leyang_two_scale_crossratio_mixing_slope_crossratio / ((n : ℝ) + 1) := by
      unfold xi_leyang_two_scale_crossratio_mixing_slope_trajectorySlope
      rw [D.xi_leyang_two_scale_crossratio_mixing_slope_scaledCrossratio_eq]
      ring
    rw [hcalc]
    exact abs_of_nonneg <|
      div_nonneg D.xi_leyang_two_scale_crossratio_mixing_slope_crossratio_nonneg hden_pos.le
  refine ⟨?_, herror⟩
  intro ε hε
  let A : ℝ := D.xi_leyang_two_scale_crossratio_mixing_slope_crossratio / ε
  obtain ⟨N, hN⟩ := exists_nat_gt A
  refine ⟨N, ?_⟩
  intro n hn
  rw [herror n]
  have hNle : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hlt : A < (n : ℝ) + 1 := by
    have hnlt : (n : ℝ) < (n : ℝ) + 1 := by linarith
    exact lt_of_lt_of_le hN (le_trans hNle (le_of_lt hnlt))
  have hnum : D.xi_leyang_two_scale_crossratio_mixing_slope_crossratio < ((n : ℝ) + 1) * ε := by
    exact (div_lt_iff₀ hε).mp (by simpa [A] using hlt)
  have hden_pos : 0 < (n : ℝ) + 1 := by positivity
  exact (div_lt_iff₀ hden_pos).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using hnum)

end

end Omega.Zeta
