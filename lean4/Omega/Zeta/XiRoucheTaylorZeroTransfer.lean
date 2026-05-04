import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- The local affine Taylor model used for the zero-transfer seed. -/
def xi_rouche_taylor_zero_transfer_affineModel
    (linearCoefficient center perturbation x : ℝ) : ℝ :=
  linearCoefficient * (x - center) + perturbation

/-- The boundary lower bound that makes the perturbation smaller than the linear Taylor part. -/
lemma xi_rouche_taylor_zero_transfer_taylor_remainder_lower_bound
    (linearCoefficient center perturbation radius x : ℝ)
    (hboundary : |x - center| = radius)
    (hsmall : |perturbation| < |linearCoefficient| * radius) :
    |perturbation| < |linearCoefficient * (x - center)| := by
  rw [abs_mul, hboundary]
  exact hsmall

/-- First Rouché seed: the transferred affine zero lies inside the controlling disk. -/
lemma xi_rouche_taylor_zero_transfer_first_rouche_application
    (linearCoefficient center perturbation radius : ℝ)
    (hlinear : linearCoefficient ≠ 0)
    (hsmall : |perturbation| < |linearCoefficient| * radius) :
    |(center - perturbation / linearCoefficient) - center| < radius := by
  have hlinear_abs : 0 < |linearCoefficient| := abs_pos.mpr hlinear
  have hquot :
      |perturbation| / |linearCoefficient| < radius := by
    rw [div_lt_iff₀ hlinear_abs]
    rwa [mul_comm]
  calc
    |(center - perturbation / linearCoefficient) - center|
        = |perturbation| / |linearCoefficient| := by
          rw [sub_sub_cancel_left, abs_neg, abs_div]
    _ < radius := hquot

/-- Second Rouché seed: the affine Taylor transfer has no second zero in the disk. -/
lemma xi_rouche_taylor_zero_transfer_second_rouche_application
    (linearCoefficient center perturbation y : ℝ)
    (hlinear : linearCoefficient ≠ 0)
    (hy :
      xi_rouche_taylor_zero_transfer_affineModel
        linearCoefficient center perturbation y = 0) :
    y = center - perturbation / linearCoefficient := by
  unfold xi_rouche_taylor_zero_transfer_affineModel at hy
  have hmul : linearCoefficient * (y - center) = -perturbation := by
    linarith
  have hy_sub : y - center = -perturbation / linearCoefficient := by
    calc
      y - center = linearCoefficient * (y - center) / linearCoefficient := by
        field_simp [hlinear]
      _ = -perturbation / linearCoefficient := by rw [hmul]
  calc
    y = (y - center) + center := by ring
    _ = -perturbation / linearCoefficient + center := by rw [hy_sub]
    _ = center - perturbation / linearCoefficient := by ring

/-- The exact drift bound for the transferred affine zero. -/
lemma xi_rouche_taylor_zero_transfer_drift_bound
    (linearCoefficient center perturbation : ℝ) :
    |(center - perturbation / linearCoefficient) - center| =
      |perturbation| / |linearCoefficient| := by
  rw [sub_sub_cancel_left, abs_neg, abs_div]

/-- Paper label: `thm:xi-rouche-taylor-zero-transfer`.

In the normalized affine Taylor seed, a perturbation that is strictly smaller than the boundary
linear term transfers the Taylor zero to a unique simple nearby zero, with the advertised drift
controlled by the perturbation divided by the nonzero linear coefficient. -/
theorem paper_xi_rouche_taylor_zero_transfer
    (linearCoefficient center perturbation radius : ℝ)
    (hlinear : linearCoefficient ≠ 0)
    (hsmall : |perturbation| < |linearCoefficient| * radius) :
    ∃! gamma : ℝ,
      xi_rouche_taylor_zero_transfer_affineModel
          linearCoefficient center perturbation gamma = 0 ∧
        |gamma - center| < radius ∧
          |gamma - center| = |perturbation| / |linearCoefficient| := by
  refine ⟨center - perturbation / linearCoefficient, ?_, ?_⟩
  · constructor
    · unfold xi_rouche_taylor_zero_transfer_affineModel
      field_simp [hlinear]
      ring
    · constructor
      · exact xi_rouche_taylor_zero_transfer_first_rouche_application
          linearCoefficient center perturbation radius hlinear hsmall
      · exact xi_rouche_taylor_zero_transfer_drift_bound
          linearCoefficient center perturbation
  · intro y hy
    exact xi_rouche_taylor_zero_transfer_second_rouche_application
      linearCoefficient center perturbation y hlinear hy.1

end

end Omega.Zeta
