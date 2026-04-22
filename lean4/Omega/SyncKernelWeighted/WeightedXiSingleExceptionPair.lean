import Mathlib.Tactic
import Mathlib.Topology.Order.IntermediateValue

namespace Omega.SyncKernelWeighted

noncomputable section

/-- The reciprocal degree-six numerator obtained after the substitution
`u = r^2`, `z = 3^(-1/2) r^(-1)`. -/
def sync_kernel_weighted_xi_single_exception_pair_N (r : ℝ) : ℝ :=
  Real.sqrt 3 * r ^ 6 - 2 * r ^ 5 - 3 * Real.sqrt 3 * r ^ 4 - 8 * r ^ 3 -
    3 * Real.sqrt 3 * r ^ 2 - 2 * r + Real.sqrt 3

/-- The completed one-variable function `Ξ`, normalized by the reciprocal sextic quotient. -/
def sync_kernel_weighted_xi_single_exception_pair_xi (r : ℝ) : ℝ :=
  sync_kernel_weighted_xi_single_exception_pair_N r / (27 * r ^ 3)

/-- The cubic in the invariant variable `t = r + r⁻¹`. -/
def sync_kernel_weighted_xi_single_exception_pair_P (t : ℝ) : ℝ :=
  Real.sqrt 3 * t ^ 3 - 2 * t ^ 2 - 6 * Real.sqrt 3 * t - 4

/-- Reciprocality of the sextic numerator. -/
lemma sync_kernel_weighted_xi_single_exception_pair_reciprocal (r : ℝ) (hr : r ≠ 0) :
    r ^ 6 * sync_kernel_weighted_xi_single_exception_pair_N (r⁻¹) =
      sync_kernel_weighted_xi_single_exception_pair_N r := by
  unfold sync_kernel_weighted_xi_single_exception_pair_N
  field_simp [hr]
  ring_nf

/-- Reduction of the sextic to the invariant cubic `P(r + r⁻¹)`. -/
lemma sync_kernel_weighted_xi_single_exception_pair_cubic_reduction (r : ℝ) (hr : r ≠ 0) :
    sync_kernel_weighted_xi_single_exception_pair_N r =
      r ^ 3 * sync_kernel_weighted_xi_single_exception_pair_P (r + r⁻¹) := by
  unfold sync_kernel_weighted_xi_single_exception_pair_N
    sync_kernel_weighted_xi_single_exception_pair_P
  field_simp [hr]
  ring_nf

/-- The sign evaluations used to isolate the three real roots of `P`. -/
lemma sync_kernel_weighted_xi_single_exception_pair_signs :
    sync_kernel_weighted_xi_single_exception_pair_P (-2) < 0 ∧
      sync_kernel_weighted_xi_single_exception_pair_P (-1) > 0 ∧
      sync_kernel_weighted_xi_single_exception_pair_P 0 < 0 ∧
      sync_kernel_weighted_xi_single_exception_pair_P 3 < 0 ∧
      sync_kernel_weighted_xi_single_exception_pair_P 4 > 0 := by
  have hsqrt3_sq : (Real.sqrt 3 : ℝ) ^ 2 = 3 := by simp
  have hsqrt3_pos : 0 < (Real.sqrt 3 : ℝ) := by positivity
  refine ⟨?_, ?_, by norm_num [sync_kernel_weighted_xi_single_exception_pair_P], ?_, ?_⟩
  · unfold sync_kernel_weighted_xi_single_exception_pair_P
    nlinarith
  · unfold sync_kernel_weighted_xi_single_exception_pair_P
    nlinarith
  · unfold sync_kernel_weighted_xi_single_exception_pair_P
    nlinarith
  · unfold sync_kernel_weighted_xi_single_exception_pair_P
    nlinarith

/-- The quadratic lift attached to a root `t > 2` of the invariant cubic. -/
def sync_kernel_weighted_xi_single_exception_pair_alpha (t : ℝ) : ℝ :=
  (t + Real.sqrt (t ^ 2 - 4)) / 2

/-- The positive exceptional root attached to `t > 2` solves `r^2 - t r + 1 = 0`. -/
lemma sync_kernel_weighted_xi_single_exception_pair_alpha_quad {t : ℝ} (ht : 2 < t) :
    let α := sync_kernel_weighted_xi_single_exception_pair_alpha t
    1 < α ∧ α ^ 2 - t * α + 1 = 0 := by
  let α := sync_kernel_weighted_xi_single_exception_pair_alpha t
  have hdisc_nonneg : 0 ≤ t ^ 2 - 4 := by nlinarith
  have hsqrt_sq : (Real.sqrt (t ^ 2 - 4)) ^ 2 = t ^ 2 - 4 := by
    exact Real.sq_sqrt hdisc_nonneg
  have hsqrt_nonneg : 0 ≤ Real.sqrt (t ^ 2 - 4) := Real.sqrt_nonneg _
  refine ⟨?_, ?_⟩
  · dsimp [α, sync_kernel_weighted_xi_single_exception_pair_alpha]
    nlinarith
  · dsimp [α, sync_kernel_weighted_xi_single_exception_pair_alpha]
    nlinarith

/-- Paper label: `thm:sync-kernel-weighted-xi-single-exception-pair`.
The sextic `N(r)` is reciprocal, descends to the cubic `P(r + r⁻¹)`, the cubic has three real
roots in `(-2,-1)`, `(-1,0)`, `(3,4)`, and the root `t₃ > 2` lifts to the exceptional reciprocal
pair `α, α⁻¹`. -/
theorem paper_sync_kernel_weighted_xi_single_exception_pair :
    (∀ r : ℝ, r ≠ 0 →
      sync_kernel_weighted_xi_single_exception_pair_xi r =
        sync_kernel_weighted_xi_single_exception_pair_N r / (27 * r ^ 3)) ∧
      (∀ r : ℝ, r ≠ 0 →
        r ^ 6 * sync_kernel_weighted_xi_single_exception_pair_N (r⁻¹) =
          sync_kernel_weighted_xi_single_exception_pair_N r) ∧
      (∀ r : ℝ, r ≠ 0 →
        sync_kernel_weighted_xi_single_exception_pair_N r =
          r ^ 3 * sync_kernel_weighted_xi_single_exception_pair_P (r + r⁻¹)) ∧
      (sync_kernel_weighted_xi_single_exception_pair_P (-2) < 0 ∧
        sync_kernel_weighted_xi_single_exception_pair_P (-1) > 0 ∧
        sync_kernel_weighted_xi_single_exception_pair_P 0 < 0 ∧
        sync_kernel_weighted_xi_single_exception_pair_P 3 < 0 ∧
        sync_kernel_weighted_xi_single_exception_pair_P 4 > 0) ∧
      ∃ t1 t2 t3 α : ℝ,
        -2 < t1 ∧ t1 < -1 ∧ sync_kernel_weighted_xi_single_exception_pair_P t1 = 0 ∧
          -1 < t2 ∧ t2 < 0 ∧ sync_kernel_weighted_xi_single_exception_pair_P t2 = 0 ∧
          3 < t3 ∧ t3 < 4 ∧ sync_kernel_weighted_xi_single_exception_pair_P t3 = 0 ∧
          α = sync_kernel_weighted_xi_single_exception_pair_alpha t3 ∧
          1 < α ∧
          α ^ 2 - t3 * α + 1 = 0 ∧
          α + α⁻¹ = t3 ∧
          sync_kernel_weighted_xi_single_exception_pair_N α = 0 ∧
          sync_kernel_weighted_xi_single_exception_pair_N α⁻¹ = 0 := by
  have hsigns := sync_kernel_weighted_xi_single_exception_pair_signs
  rcases hsigns with ⟨hPneg2, hPneg1, hP0, hP3, hP4⟩
  have hsigns' :
      sync_kernel_weighted_xi_single_exception_pair_P (-2) < 0 ∧
        sync_kernel_weighted_xi_single_exception_pair_P (-1) > 0 ∧
        sync_kernel_weighted_xi_single_exception_pair_P 0 < 0 ∧
        sync_kernel_weighted_xi_single_exception_pair_P 3 < 0 ∧
        sync_kernel_weighted_xi_single_exception_pair_P 4 > 0 := by
    exact ⟨hPneg2, hPneg1, hP0, hP3, hP4⟩
  have hP_cont : Continuous sync_kernel_weighted_xi_single_exception_pair_P := by
    unfold sync_kernel_weighted_xi_single_exception_pair_P
    continuity
  have hnegP_cont : Continuous fun t : ℝ => -sync_kernel_weighted_xi_single_exception_pair_P t := by
    continuity
  have hzero1_mem :
      (0 : ℝ) ∈ Set.Ioo (sync_kernel_weighted_xi_single_exception_pair_P (-2))
        (sync_kernel_weighted_xi_single_exception_pair_P (-1)) := by
    exact ⟨hPneg2, hPneg1⟩
  rcases intermediate_value_Ioo (show (-2 : ℝ) ≤ -1 by norm_num) hP_cont.continuousOn hzero1_mem
    with ⟨t1, ht1, hPt1⟩
  have hzero2_mem :
      (0 : ℝ) ∈ Set.Ioo (-(sync_kernel_weighted_xi_single_exception_pair_P (-1)))
        (-(sync_kernel_weighted_xi_single_exception_pair_P 0)) := by
    constructor <;> linarith
  rcases intermediate_value_Ioo (show (-1 : ℝ) ≤ 0 by norm_num) hnegP_cont.continuousOn hzero2_mem
    with ⟨t2, ht2, hnegPt2⟩
  have hPt2 : sync_kernel_weighted_xi_single_exception_pair_P t2 = 0 := by linarith
  have hzero3_mem :
      (0 : ℝ) ∈ Set.Ioo (sync_kernel_weighted_xi_single_exception_pair_P 3)
        (sync_kernel_weighted_xi_single_exception_pair_P 4) := by
    exact ⟨hP3, hP4⟩
  rcases intermediate_value_Ioo (show (3 : ℝ) ≤ 4 by norm_num) hP_cont.continuousOn hzero3_mem with
    ⟨t3, ht3, hPt3⟩
  have ht3_gt2 : 2 < t3 := by linarith [ht3.1]
  have hαdata := sync_kernel_weighted_xi_single_exception_pair_alpha_quad ht3_gt2
  rcases hαdata with ⟨hαgt1, hαquad⟩
  let α := sync_kernel_weighted_xi_single_exception_pair_alpha t3
  have hαne : α ≠ 0 := by linarith
  have hsum :
      α + α⁻¹ = t3 := by
    have hmul : α * (α + α⁻¹ - t3) = 0 := by
      calc
        α * (α + α⁻¹ - t3) = α ^ 2 + α * α⁻¹ - t3 * α := by ring
        _ = α ^ 2 + 1 - t3 * α := by simp [hαne]
        _ = α ^ 2 - t3 * α + 1 := by ring
        _ = 0 := hαquad
    have hinner : α + α⁻¹ - t3 = 0 := (mul_eq_zero.mp hmul).resolve_left hαne
    linarith
  have hNα :
      sync_kernel_weighted_xi_single_exception_pair_N α = 0 := by
    calc
      sync_kernel_weighted_xi_single_exception_pair_N α =
          α ^ 3 * sync_kernel_weighted_xi_single_exception_pair_P (α + α⁻¹) := by
            simpa [α] using
              sync_kernel_weighted_xi_single_exception_pair_cubic_reduction α hαne
      _ = α ^ 3 * sync_kernel_weighted_xi_single_exception_pair_P t3 := by rw [hsum]
      _ = 0 := by rw [hPt3]; ring
  have hNinv :
      sync_kernel_weighted_xi_single_exception_pair_N α⁻¹ = 0 := by
    calc
      sync_kernel_weighted_xi_single_exception_pair_N α⁻¹ =
          (α⁻¹) ^ 3 *
            sync_kernel_weighted_xi_single_exception_pair_P (α⁻¹ + (α⁻¹)⁻¹) := by
              simpa [α] using
                sync_kernel_weighted_xi_single_exception_pair_cubic_reduction α⁻¹
                  (inv_ne_zero hαne)
      _ = (α⁻¹) ^ 3 * sync_kernel_weighted_xi_single_exception_pair_P t3 := by
            simp [hsum, add_comm]
      _ = 0 := by rw [hPt3]; ring
  refine ⟨?_, sync_kernel_weighted_xi_single_exception_pair_reciprocal,
    sync_kernel_weighted_xi_single_exception_pair_cubic_reduction, hsigns', ?_⟩
  · intro r hr
    rfl
  · refine ⟨t1, t2, t3, α, ht1.1, ht1.2, hPt1, ht2.1, ht2.2, hPt2, ht3.1, ht3.2, hPt3,
      rfl, hαgt1, hαquad, hsum, hNα, hNinv⟩

end

end Omega.SyncKernelWeighted
