import Mathlib.Tactic

namespace Omega.POM

/-- Concrete balanced bucket data for the remainder-bit Rényi compression law. The `q` remainder
classes have sizes `d_min` or `d_min + 1`, with exactly `r` large classes. -/
structure RemainderBitsAllRenyiCompressionLawData where
  q : ℕ
  r : ℕ
  dMin : ℕ
  q_ge_two : 2 ≤ q
  r_lt_q : r < q

namespace RemainderBitsAllRenyiCompressionLawData

/-- Number of remainder classes of size `d_min`. -/
def lowerBucketCount (D : RemainderBitsAllRenyiCompressionLawData) : ℕ :=
  D.q - D.r

/-- Number of remainder classes of size `d_min + 1`. -/
def upperBucketCount (D : RemainderBitsAllRenyiCompressionLawData) : ℕ :=
  D.r

/-- The `q`-moment of the balanced bucket split. -/
def Sq (D : RemainderBitsAllRenyiCompressionLawData) : ℝ :=
  (D.lowerBucketCount : ℝ) * (D.dMin : ℝ) ^ D.q +
    (D.upperBucketCount : ℝ) * ((D.dMin + 1 : ℕ) : ℝ) ^ D.q

/-- The normalized `q`-moment. -/
noncomputable def Mq (D : RemainderBitsAllRenyiCompressionLawData) : ℝ :=
  D.Sq / D.q

/-- Jensen/concentration squeeze for the balanced `q`-moment. -/
def SqBounds (D : RemainderBitsAllRenyiCompressionLawData) : Prop :=
  (D.q : ℝ) * (D.dMin : ℝ) ^ D.q ≤ D.Sq ∧
    D.Sq ≤ (D.q : ℝ) * (((D.dMin + 1 : ℕ) : ℝ) ^ D.q)

/-- The same squeeze after normalizing by the number of remainder classes. -/
def MqBounds (D : RemainderBitsAllRenyiCompressionLawData) : Prop :=
  (D.dMin : ℝ) ^ D.q ≤ D.Mq ∧
    D.Mq ≤ (((D.dMin + 1 : ℕ) : ℝ) ^ D.q)

/-- Exact first-order correction term relative to the uniform `d_min` bucket law. -/
def asymptoticRatio (D : RemainderBitsAllRenyiCompressionLawData) : Prop :=
  ∃ correction : ℝ,
    D.Mq = (D.dMin : ℝ) ^ D.q + correction ∧
      |correction| ≤
        (D.r : ℝ) *
            ((((D.dMin + 1 : ℕ) : ℝ) ^ D.q) - (D.dMin : ℝ) ^ D.q) /
          D.q

/-- The normalized moment stays between the two adjacent `q`-power scales, so the ambient
`q`-power growth rate is unchanged by the balanced remainder split. -/
def rootRateInvariant (D : RemainderBitsAllRenyiCompressionLawData) : Prop :=
  (D.dMin : ℝ) ^ D.q / (((D.dMin + 1 : ℕ) : ℝ) ^ D.q) ≤
      D.Mq / (((D.dMin + 1 : ℕ) : ℝ) ^ D.q) ∧
    D.Mq / (((D.dMin + 1 : ℕ) : ℝ) ^ D.q) ≤ 1

end RemainderBitsAllRenyiCompressionLawData

open RemainderBitsAllRenyiCompressionLawData

private lemma q_pos_real (D : RemainderBitsAllRenyiCompressionLawData) : 0 < (D.q : ℝ) := by
  exact_mod_cast lt_of_lt_of_le (show 0 < (2 : ℕ) by decide) D.q_ge_two

private lemma bucket_count_sum (D : RemainderBitsAllRenyiCompressionLawData) :
    (D.lowerBucketCount : ℝ) + (D.upperBucketCount : ℝ) = D.q := by
  exact_mod_cast Nat.sub_add_cancel (Nat.le_of_lt D.r_lt_q)

private lemma lower_le_upper_pow (D : RemainderBitsAllRenyiCompressionLawData) :
    (D.dMin : ℝ) ^ D.q ≤ (((D.dMin + 1 : ℕ) : ℝ) ^ D.q) := by
  exact_mod_cast Nat.pow_le_pow_left (Nat.le_succ D.dMin) D.q

private lemma sq_bounds (D : RemainderBitsAllRenyiCompressionLawData) : D.SqBounds := by
  let a : ℝ := (D.dMin : ℝ) ^ D.q
  let b : ℝ := (((D.dMin + 1 : ℕ) : ℝ) ^ D.q)
  let α : ℝ := D.lowerBucketCount
  let β : ℝ := D.upperBucketCount
  have hab : a ≤ b := lower_le_upper_pow D
  have hαβ : α + β = D.q := bucket_count_sum D
  have hα_nonneg : 0 ≤ α := by positivity
  have hβ_nonneg : 0 ≤ β := by positivity
  constructor
  · have hmain : (D.q : ℝ) * a ≤ α * a + β * b := by
      calc
        (D.q : ℝ) * a = (α + β) * a := by rw [hαβ]
        _ = α * a + β * a := by ring
        _ ≤ α * a + β * b := by gcongr
    simpa [RemainderBitsAllRenyiCompressionLawData.Sq, a, b, α, β] using hmain
  · have hmain : α * a + β * b ≤ (D.q : ℝ) * b := by
      calc
        α * a + β * b ≤ α * b + β * b := by gcongr
        _ = (α + β) * b := by ring
        _ = (D.q : ℝ) * b := by rw [hαβ]
    simpa [RemainderBitsAllRenyiCompressionLawData.Sq, a, b, α, β] using hmain

private lemma mq_bounds (D : RemainderBitsAllRenyiCompressionLawData) : D.MqBounds := by
  have hqpos := q_pos_real D
  rcases sq_bounds D with ⟨hLower, hUpper⟩
  constructor
  · rw [RemainderBitsAllRenyiCompressionLawData.Mq]
    rw [le_div_iff₀ hqpos]
    simpa [mul_comm] using hLower
  · rw [RemainderBitsAllRenyiCompressionLawData.Mq]
    rw [div_le_iff₀ hqpos]
    simpa [mul_comm] using hUpper

private lemma mq_correction (D : RemainderBitsAllRenyiCompressionLawData) : D.asymptoticRatio := by
  let a : ℝ := (D.dMin : ℝ) ^ D.q
  let b : ℝ := (((D.dMin + 1 : ℕ) : ℝ) ^ D.q)
  let corr : ℝ := (D.r : ℝ) * (b - a) / D.q
  have hqpos := q_pos_real D
  have hsum : (D.lowerBucketCount : ℝ) + (D.r : ℝ) = D.q := by
    simpa [RemainderBitsAllRenyiCompressionLawData.upperBucketCount] using bucket_count_sum D
  have hab : a ≤ b := lower_le_upper_pow D
  refine ⟨corr, ?_, ?_⟩
  · rw [RemainderBitsAllRenyiCompressionLawData.Mq, RemainderBitsAllRenyiCompressionLawData.Sq]
    change
      (((D.lowerBucketCount : ℝ) * a + (D.r : ℝ) * b) / D.q) =
        a + ((D.r : ℝ) * (b - a) / D.q)
    have hrewrite :
        (D.lowerBucketCount : ℝ) * a + (D.r : ℝ) * b =
          (D.q : ℝ) * a + (D.r : ℝ) * (b - a) := by
      rw [← hsum]
      ring
    rw [hrewrite]
    field_simp [hqpos.ne']
  · have hcorr_nonneg : 0 ≤ corr := by
      have hdiff_nonneg : 0 ≤ b - a := sub_nonneg.mpr hab
      have hr_nonneg : 0 ≤ (D.r : ℝ) := by positivity
      have hq_nonneg : 0 ≤ (D.q : ℝ) := le_of_lt hqpos
      unfold corr
      exact div_nonneg (mul_nonneg hr_nonneg hdiff_nonneg) hq_nonneg
    rw [abs_of_nonneg hcorr_nonneg]

private lemma mq_root_rate (D : RemainderBitsAllRenyiCompressionLawData) : D.rootRateInvariant := by
  let b : ℝ := (((D.dMin + 1 : ℕ) : ℝ) ^ D.q)
  have hbpos : 0 < b := by
    unfold b
    have : (0 : ℝ) < (((D.dMin + 1 : ℕ) : ℝ)) := by
      exact_mod_cast Nat.succ_pos D.dMin
    exact pow_pos this D.q
  have hbinv_nonneg : 0 ≤ b⁻¹ := by positivity
  rcases mq_bounds D with ⟨hLower, hUpper⟩
  constructor
  · have hscaled := mul_le_mul_of_nonneg_right hLower hbinv_nonneg
    simpa [div_eq_mul_inv, b, mul_comm, mul_left_comm, mul_assoc] using hscaled
  · have hscaled := mul_le_mul_of_nonneg_right hUpper hbinv_nonneg
    calc
      D.Mq / b = D.Mq * b⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ (((D.dMin + 1 : ℕ) : ℝ) ^ D.q) * b⁻¹ := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using hscaled
      _ = 1 := by
        unfold b
        field_simp [hbpos.ne']

/-- Balanced floor/ceiling splitting across the remainder classes squeezes the `q`-moment and its
normalized version, yields the explicit remainder correction term, and preserves the ambient
`q`-power growth scale.
    thm:pom-remainder-bits-all-renyi-compression-law -/
theorem paper_pom_remainder_bits_all_renyi_compression_law
    (D : RemainderBitsAllRenyiCompressionLawData) :
    D.SqBounds ∧ D.MqBounds ∧ D.asymptoticRatio ∧ D.rootRateInvariant := by
  exact ⟨sq_bounds D, mq_bounds D, mq_correction D, mq_root_rate D⟩

end Omega.POM
