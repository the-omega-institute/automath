import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/-- Concrete finite offslice data: each modulus `|a_j|` is the exponential of the corresponding
real-part deviation. -/
structure xi_offslice_realpart_sum_law_data where
  n : ℕ
  rePart : Fin n → ℝ
  a : Fin n → ℝ
  L : ℝ
  hL : 0 < L
  ha : ∀ j, |a j| = Real.exp (-(2 * rePart j - 1) * L)

/-- The total logarithmic offslice weight. -/
def xi_offslice_realpart_sum_law_weight (h : xi_offslice_realpart_sum_law_data) : ℝ :=
  ∑ j, Real.log (1 / |h.a j|)

/-- The origin modulus of the finite Blaschke product. -/
def xi_offslice_realpart_sum_law_origin_modulus (h : xi_offslice_realpart_sum_law_data) : ℝ :=
  ∏ j, |h.a j|

/-- The total deviation of the real parts from the critical line. -/
def xi_offslice_realpart_sum_law_total_deviation (h : xi_offslice_realpart_sum_law_data) : ℝ :=
  ∑ j, (h.rePart j - (1 / 2 : ℝ))

/-- The weight equals the sum of the exponential real-part deviations. -/
def xi_offslice_realpart_sum_law_data.weight_formula
    (h : xi_offslice_realpart_sum_law_data) : Prop :=
  xi_offslice_realpart_sum_law_weight h = h.L * ∑ j, (2 * h.rePart j - 1)

/-- The origin modulus packages the same data as the logarithmic weight. -/
def xi_offslice_realpart_sum_law_data.origin_modulus_formula
    (h : xi_offslice_realpart_sum_law_data) : Prop :=
  -Real.log (xi_offslice_realpart_sum_law_origin_modulus h) =
    xi_offslice_realpart_sum_law_weight h

/-- Dividing by `2L` converts the weight and the origin modulus into the total real-part
deviation from the critical line. -/
def xi_offslice_realpart_sum_law_data.total_deviation_formula
    (h : xi_offslice_realpart_sum_law_data) : Prop :=
  xi_offslice_realpart_sum_law_total_deviation h =
      xi_offslice_realpart_sum_law_weight h / (2 * h.L) ∧
    xi_offslice_realpart_sum_law_total_deviation h =
      -Real.log (xi_offslice_realpart_sum_law_origin_modulus h) / (2 * h.L)

/-- Paper label: `thm:xi-offslice-realpart-sum-law`. The logarithmic Blaschke weight, the origin
modulus, and the total deviation from the critical line are all exact restatements of the same
finite exponential identity. -/
theorem paper_xi_offslice_realpart_sum_law (h : xi_offslice_realpart_sum_law_data) :
    h.weight_formula ∧ h.origin_modulus_formula ∧ h.total_deviation_formula := by
  have hterm :
      ∀ j, Real.log (1 / |h.a j|) = (2 * h.rePart j - 1) * h.L := by
    intro j
    rw [h.ha j, one_div]
    have hexp_inv :
        (Real.exp (-(2 * h.rePart j - 1) * h.L))⁻¹ =
          Real.exp ((2 * h.rePart j - 1) * h.L) := by
      rw [← Real.exp_neg]
      ring_nf
    rw [hexp_inv, Real.log_exp]
  have hweight :
      xi_offslice_realpart_sum_law_weight h = h.L * ∑ j, (2 * h.rePart j - 1) := by
    unfold xi_offslice_realpart_sum_law_weight
    calc
      ∑ j, Real.log (1 / |h.a j|) = ∑ j, ((2 * h.rePart j - 1) * h.L) := by
        refine Finset.sum_congr rfl ?_
        intro j hj
        exact hterm j
      _ = h.L * ∑ j, (2 * h.rePart j - 1) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro j hj
        ring
  have hnonzero : ∀ j, |h.a j| ≠ 0 := by
    intro j
    rw [h.ha j]
    exact Real.exp_ne_zero _
  have hlogprod :
      Real.log (xi_offslice_realpart_sum_law_origin_modulus h) =
        ∑ j, Real.log |h.a j| := by
    unfold xi_offslice_realpart_sum_law_origin_modulus
    rw [Real.log_prod]
    intro j hj
    exact hnonzero j
  have horigin :
      -Real.log (xi_offslice_realpart_sum_law_origin_modulus h) =
        xi_offslice_realpart_sum_law_weight h := by
    calc
      -Real.log (xi_offslice_realpart_sum_law_origin_modulus h) =
          -(∑ j, Real.log |h.a j|) := by rw [hlogprod]
      _ = ∑ j, Real.log (1 / |h.a j|) := by
        rw [show -(∑ j, Real.log |h.a j|) = ∑ j, -Real.log |h.a j| by
          rw [← Finset.sum_neg_distrib]]
        refine Finset.sum_congr rfl ?_
        intro j hj
        rw [show (1 / |h.a j|) = (|h.a j|)⁻¹ by simp [one_div], Real.log_inv]
      _ = xi_offslice_realpart_sum_law_weight h := by
        rfl
  have hsum :
      ∑ j, (2 * h.rePart j - 1) = 2 * ∑ j, (h.rePart j - (1 / 2 : ℝ)) := by
    calc
      ∑ j, (2 * h.rePart j - 1) = ∑ j, (2 * (h.rePart j - (1 / 2 : ℝ))) := by
        refine Finset.sum_congr rfl ?_
        intro j hj
        ring
      _ = 2 * ∑ j, (h.rePart j - (1 / 2 : ℝ)) := by
        symm
        rw [Finset.mul_sum]
  have hweight_total :
      xi_offslice_realpart_sum_law_weight h =
        (2 * h.L) * xi_offslice_realpart_sum_law_total_deviation h := by
    calc
      xi_offslice_realpart_sum_law_weight h = h.L * ∑ j, (2 * h.rePart j - 1) := hweight
      _ = h.L * (2 * ∑ j, (h.rePart j - (1 / 2 : ℝ))) := by rw [hsum]
      _ = (2 * h.L) * xi_offslice_realpart_sum_law_total_deviation h := by
        unfold xi_offslice_realpart_sum_law_total_deviation
        ring
  have htwoL_ne : 2 * h.L ≠ 0 := by
    nlinarith [h.hL]
  have htotal_from_weight :
      xi_offslice_realpart_sum_law_total_deviation h =
        xi_offslice_realpart_sum_law_weight h / (2 * h.L) := by
    apply (eq_div_iff htwoL_ne).2
    calc
      xi_offslice_realpart_sum_law_total_deviation h * (2 * h.L) =
          (2 * h.L) * xi_offslice_realpart_sum_law_total_deviation h := by ring
      _ = xi_offslice_realpart_sum_law_weight h := hweight_total.symm
  have htotal_from_origin :
      xi_offslice_realpart_sum_law_total_deviation h =
        -Real.log (xi_offslice_realpart_sum_law_origin_modulus h) / (2 * h.L) := by
    rw [horigin]
    exact htotal_from_weight
  exact ⟨hweight, horigin, ⟨htotal_from_weight, htotal_from_origin⟩⟩

end

end Omega.Zeta
