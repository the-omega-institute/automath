import Mathlib.Analysis.SpecialFunctions.Pow.Real
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

/-- The off-critical coordinate attached to the exceptional real root `α > 1`. -/
def sync_kernel_weighted_xi_exception_coordinate_beta (α : ℝ) : ℝ :=
  Real.log α / Real.log 3

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

/-- Paper label: `thm:sync-kernel-weighted-xi-exception-coordinate`. The exceptional real zero
pair is parameterized by `β = log α / log 3`, while the two remaining cubic roots in `(-2,0)`
produce critical-line angle coordinates through `t = 2 cos θ`. -/
theorem paper_sync_kernel_weighted_xi_exception_coordinate :
    ∃ t1 t2 t3 α β θ1 θ2 : ℝ,
      -2 < t1 ∧
      t1 < -1 ∧
      sync_kernel_weighted_xi_single_exception_pair_P t1 = 0 ∧
      -1 < t2 ∧
      t2 < 0 ∧
      sync_kernel_weighted_xi_single_exception_pair_P t2 = 0 ∧
      3 < t3 ∧
      t3 < 4 ∧
      sync_kernel_weighted_xi_single_exception_pair_P t3 = 0 ∧
      α = sync_kernel_weighted_xi_single_exception_pair_alpha t3 ∧
      β = sync_kernel_weighted_xi_exception_coordinate_beta α ∧
      1 < α ∧
      α + α⁻¹ = t3 ∧
      0 < β ∧
      Real.rpow 3 β = α ∧
      Real.rpow 3 (-β) = α⁻¹ ∧
      sync_kernel_weighted_xi_single_exception_pair_N (Real.rpow 3 β) = 0 ∧
      sync_kernel_weighted_xi_single_exception_pair_N (Real.rpow 3 (-β)) = 0 ∧
      θ1 ∈ Set.Ioo (Real.pi / 2) Real.pi ∧
      2 * Real.cos θ1 = t1 ∧
      θ2 ∈ Set.Ioo (Real.pi / 2) Real.pi ∧
      2 * Real.cos θ2 = t2 := by
  rcases paper_sync_kernel_weighted_xi_single_exception_pair with
    ⟨_, _, _, _, t1, t2, t3, α, ht1lo, ht1hi, hPt1, ht2lo, ht2hi, hPt2, ht3lo, ht3hi, hPt3,
      hαrfl, hαgt1, _, hsum, hNα, hNinv⟩
  let β := sync_kernel_weighted_xi_exception_coordinate_beta α
  have hthree_pos : 0 < (3 : ℝ) := by norm_num
  have hlog3_pos : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlog3_ne : Real.log 3 ≠ 0 := hlog3_pos.ne'
  have hlogα_pos : 0 < Real.log α := Real.log_pos hαgt1
  have hβpos : 0 < β := by
    dsimp [β, sync_kernel_weighted_xi_exception_coordinate_beta]
    exact div_pos hlogα_pos hlog3_pos
  have hβeq : β = sync_kernel_weighted_xi_exception_coordinate_beta α := rfl
  have hpowβ : Real.rpow 3 β = α := by
    calc
      Real.rpow 3 β = Real.exp (Real.log 3 * β) := by
        simpa [mul_comm] using (Real.rpow_def_of_pos hthree_pos β)
      _ = Real.exp (Real.log α) := by
        congr 1
        dsimp [β, sync_kernel_weighted_xi_exception_coordinate_beta]
        field_simp [hlog3_ne]
      _ = α := by
        rw [Real.exp_log (lt_trans zero_lt_one hαgt1)]
  have hpowNeg : Real.rpow 3 (-β) = α⁻¹ := by
    calc
      Real.rpow 3 (-β) = (Real.rpow 3 β)⁻¹ := by
        simpa using (Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3) β)
      _ = α⁻¹ := by rw [hpowβ]
  have hNpowβ :
      sync_kernel_weighted_xi_single_exception_pair_N (Real.rpow 3 β) = 0 := by
    rw [hpowβ]
    exact hNα
  have hNpowNeg :
      sync_kernel_weighted_xi_single_exception_pair_N (Real.rpow 3 (-β)) = 0 := by
    rw [hpowNeg]
    exact hNinv
  have hnegcos_cont : Continuous fun θ : ℝ => -2 * Real.cos θ := by
    continuity
  have hpi_half_le_pi : Real.pi / 2 ≤ Real.pi := by
    nlinarith [Real.pi_pos]
  have ht1_mem :
      -t1 ∈ Set.Ioo ((fun θ : ℝ => -2 * Real.cos θ) (Real.pi / 2))
        ((fun θ : ℝ => -2 * Real.cos θ) Real.pi) := by
    constructor
    · have ht1neg : 0 < -t1 := by
        have ht1lt0 : t1 < 0 := lt_trans ht1hi (by norm_num)
        linarith
      simpa [Real.cos_pi_div_two] using ht1neg
    · have ht1lt2 : -t1 < 2 := by linarith
      simpa [Real.cos_pi] using ht1lt2
  rcases intermediate_value_Ioo hpi_half_le_pi hnegcos_cont.continuousOn ht1_mem with
    ⟨θ1, hθ1, hθ1eq⟩
  have hθ1eq' : 2 * Real.cos θ1 = t1 := by linarith
  have ht2_mem :
      -t2 ∈ Set.Ioo ((fun θ : ℝ => -2 * Real.cos θ) (Real.pi / 2))
        ((fun θ : ℝ => -2 * Real.cos θ) Real.pi) := by
    constructor
    · have ht2neg : 0 < -t2 := by linarith
      simpa [Real.cos_pi_div_two] using ht2neg
    · have ht2lt2 : -t2 < 2 := by linarith
      simpa [Real.cos_pi] using ht2lt2
  rcases intermediate_value_Ioo hpi_half_le_pi hnegcos_cont.continuousOn ht2_mem with
    ⟨θ2, hθ2, hθ2eq⟩
  have hθ2eq' : 2 * Real.cos θ2 = t2 := by linarith
  refine ⟨t1, t2, t3, α, β, θ1, θ2, ht1lo, ht1hi, hPt1, ht2lo, ht2hi, hPt2, ht3lo, ht3hi,
    hPt3, hαrfl, hβeq, hαgt1, hsum, hβpos, hpowβ, hpowNeg, hNpowβ, hNpowNeg, hθ1, hθ1eq',
    hθ2, hθ2eq'⟩

end

end Omega.SyncKernelWeighted
