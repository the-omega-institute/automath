import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/-- Concrete finite disk-zero data for the radial defect package.  The radii are the moduli of the
disk zeros, listed with multiplicity weights, and `realRoot` records the corresponding real
Joukowsky parameter in the over-the-edge real-root normalization. -/
structure xi_phil_defect_weight_blaschke_origin_data where
  n : ℕ
  radius : Fin n → ℝ
  multiplicity : Fin n → ℕ
  realRoot : Fin n → ℝ
  radius_pos : ∀ j, 0 < radius j
  radius_lt_one : ∀ j, radius j < 1
  joukowsky_arcosh :
    ∀ j, Real.log (1 / radius j) = Real.arcosh (|realRoot j| / 2)

/-- The origin modulus of the finite Blaschke product assembled from the listed disk-zero radii. -/
def xi_phil_defect_weight_blaschke_origin_origin_modulus
    (D : xi_phil_defect_weight_blaschke_origin_data) : ℝ :=
  ∏ j, D.radius j ^ D.multiplicity j

/-- The logarithmic radial defect weight. -/
def xi_phil_defect_weight_blaschke_origin_weight
    (D : xi_phil_defect_weight_blaschke_origin_data) : ℝ :=
  ∑ j, (D.multiplicity j : ℝ) * Real.log (1 / D.radius j)

/-- The over-the-edge real-root arcosh restatement of the same radial defect weight. -/
def xi_phil_defect_weight_blaschke_origin_arcosh_weight
    (D : xi_phil_defect_weight_blaschke_origin_data) : ℝ :=
  ∑ j, (D.multiplicity j : ℝ) * Real.arcosh (|D.realRoot j| / 2)

/-- Blaschke-origin law: the finite product modulus and its logarithmic weight agree. -/
def xi_phil_defect_weight_blaschke_origin_blaschke_law
    (D : xi_phil_defect_weight_blaschke_origin_data) : Prop :=
  -Real.log (xi_phil_defect_weight_blaschke_origin_origin_modulus D) =
    xi_phil_defect_weight_blaschke_origin_weight D

/-- Arcosh law: the Joukowsky real-root correspondence rewrites the same weight. -/
def xi_phil_defect_weight_blaschke_origin_arcosh_law
    (D : xi_phil_defect_weight_blaschke_origin_data) : Prop :=
  xi_phil_defect_weight_blaschke_origin_weight D =
      xi_phil_defect_weight_blaschke_origin_arcosh_weight D ∧
    -Real.log (xi_phil_defect_weight_blaschke_origin_origin_modulus D) =
      xi_phil_defect_weight_blaschke_origin_arcosh_weight D

private lemma xi_phil_defect_weight_blaschke_origin_log_pow_inv
    (r : ℝ) (m : ℕ) :
    -Real.log (r ^ m) = (m : ℝ) * Real.log (1 / r) := by
  rw [Real.log_pow]
  rw [show Real.log (1 / r) = -Real.log r by
    rw [one_div, Real.log_inv]]
  ring

/-- Paper label: `prop:xi-phiL-defect-weight-blaschke-origin`. -/
theorem paper_xi_phil_defect_weight_blaschke_origin
    (D : xi_phil_defect_weight_blaschke_origin_data) :
    xi_phil_defect_weight_blaschke_origin_blaschke_law D ∧
      xi_phil_defect_weight_blaschke_origin_arcosh_law D := by
  have hterm_ne : ∀ j, D.radius j ^ D.multiplicity j ≠ 0 := by
    intro j
    exact pow_ne_zero _ (ne_of_gt (D.radius_pos j))
  have hblaschke :
      xi_phil_defect_weight_blaschke_origin_blaschke_law D := by
    unfold xi_phil_defect_weight_blaschke_origin_blaschke_law
    unfold xi_phil_defect_weight_blaschke_origin_origin_modulus
    unfold xi_phil_defect_weight_blaschke_origin_weight
    calc
      -Real.log (∏ j, D.radius j ^ D.multiplicity j) =
          -(∑ j, Real.log (D.radius j ^ D.multiplicity j)) := by
            rw [Real.log_prod]
            intro j hj
            exact hterm_ne j
      _ = ∑ j, -Real.log (D.radius j ^ D.multiplicity j) := by
            rw [← Finset.sum_neg_distrib]
      _ = ∑ j, (D.multiplicity j : ℝ) * Real.log (1 / D.radius j) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            exact xi_phil_defect_weight_blaschke_origin_log_pow_inv
              (D.radius j) (D.multiplicity j)
  have harcosh_weight :
      xi_phil_defect_weight_blaschke_origin_weight D =
        xi_phil_defect_weight_blaschke_origin_arcosh_weight D := by
    unfold xi_phil_defect_weight_blaschke_origin_weight
    unfold xi_phil_defect_weight_blaschke_origin_arcosh_weight
    refine Finset.sum_congr rfl ?_
    intro j hj
    rw [D.joukowsky_arcosh j]
  exact ⟨hblaschke, harcosh_weight, hblaschke.trans harcosh_weight⟩

end

end Omega.Zeta
