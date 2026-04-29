import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic

namespace Omega.Zeta

noncomputable def xi_time_part9ze_negative_zero_temperature_freezing_partition
    {ι : Type} (S : Finset ι) (d : ι → ℝ) (q : ℝ) : ℝ :=
  Finset.sum S fun i => Real.exp (q * Real.log (d i))

noncomputable def xi_time_part9ze_negative_zero_temperature_freezing_normalized
    {ι : Type} (S : Finset ι) (d : ι → ℝ) (dmin q : ℝ) : ℝ :=
  Real.exp (-q * Real.log dmin) *
    xi_time_part9ze_negative_zero_temperature_freezing_partition S d q

noncomputable def xi_time_part9ze_negative_zero_temperature_freezing_minimizerCard
    {ι : Type} [DecidableEq ι] (S : Finset ι) (d : ι → ℝ) (dmin : ℝ) : ℝ :=
  ((S.filter fun i => d i = dmin).card : ℝ)

lemma xi_time_part9ze_negative_zero_temperature_freezing_partition_pos
    {ι : Type} {S : Finset ι} {d : ι → ℝ} (q : ℝ) (hS : S.Nonempty) :
    0 < xi_time_part9ze_negative_zero_temperature_freezing_partition S d q := by
  unfold xi_time_part9ze_negative_zero_temperature_freezing_partition
  exact Finset.sum_pos (fun i _ => Real.exp_pos _) hS

lemma xi_time_part9ze_negative_zero_temperature_freezing_normalized_pos
    {ι : Type} {S : Finset ι} {d : ι → ℝ} {dmin q : ℝ} (hS : S.Nonempty) :
    0 < xi_time_part9ze_negative_zero_temperature_freezing_normalized S d dmin q := by
  unfold xi_time_part9ze_negative_zero_temperature_freezing_normalized
  exact mul_pos (Real.exp_pos _) <|
    xi_time_part9ze_negative_zero_temperature_freezing_partition_pos q hS

lemma xi_time_part9ze_negative_zero_temperature_freezing_normalized_eq_sum
    {ι : Type} (S : Finset ι) (d : ι → ℝ) (dmin q : ℝ) :
    xi_time_part9ze_negative_zero_temperature_freezing_normalized S d dmin q =
      Finset.sum S fun i => Real.exp (q * (Real.log (d i) - Real.log dmin)) := by
  unfold xi_time_part9ze_negative_zero_temperature_freezing_normalized
    xi_time_part9ze_negative_zero_temperature_freezing_partition
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [← Real.exp_add]
  congr 1
  ring

lemma xi_time_part9ze_negative_zero_temperature_freezing_partition_eq_exp_mul_normalized
    {ι : Type} (S : Finset ι) (d : ι → ℝ) (dmin q : ℝ) :
    xi_time_part9ze_negative_zero_temperature_freezing_partition S d q =
      Real.exp (q * Real.log dmin) *
        xi_time_part9ze_negative_zero_temperature_freezing_normalized S d dmin q := by
  unfold xi_time_part9ze_negative_zero_temperature_freezing_normalized
  calc
    xi_time_part9ze_negative_zero_temperature_freezing_partition S d q =
        1 * xi_time_part9ze_negative_zero_temperature_freezing_partition S d q := by
        rw [one_mul]
    _ = (Real.exp (q * Real.log dmin) * Real.exp (-q * Real.log dmin)) *
        xi_time_part9ze_negative_zero_temperature_freezing_partition S d q := by
        rw [← Real.exp_add]
        have hzero : q * Real.log dmin + -q * Real.log dmin = 0 := by ring
        rw [hzero, Real.exp_zero]
    _ = Real.exp (q * Real.log dmin) *
        (Real.exp (-q * Real.log dmin) *
          xi_time_part9ze_negative_zero_temperature_freezing_partition S d q) := by
        ring

lemma xi_time_part9ze_negative_zero_temperature_freezing_minimizerCard_pos
    {ι : Type} [DecidableEq ι] {S : Finset ι} {d : ι → ℝ} {dmin : ℝ}
    (hhit : ∃ i ∈ S, d i = dmin) :
    0 < xi_time_part9ze_negative_zero_temperature_freezing_minimizerCard S d dmin := by
  unfold xi_time_part9ze_negative_zero_temperature_freezing_minimizerCard
  rcases hhit with ⟨i, hiS, hi⟩
  exact_mod_cast Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨hiS, hi⟩⟩

lemma xi_time_part9ze_negative_zero_temperature_freezing_normalized_tendsto
    {ι : Type} [DecidableEq ι] (S : Finset ι) (d : ι → ℝ) (dmin : ℝ)
    (hpos : ∀ i ∈ S, 0 < d i) (hmin : ∀ i ∈ S, dmin ≤ d i)
    (hhit : ∃ i ∈ S, d i = dmin) :
    Filter.Tendsto
      (fun q : ℝ => xi_time_part9ze_negative_zero_temperature_freezing_normalized S d dmin q)
      Filter.atBot
      (nhds (xi_time_part9ze_negative_zero_temperature_freezing_minimizerCard S d dmin)) := by
  have hdmin_pos : 0 < dmin := by
    rcases hhit with ⟨i, hiS, hi⟩
    simpa [hi] using hpos i hiS
  have hterm :
      ∀ i ∈ S,
        Filter.Tendsto
          (fun q : ℝ => Real.exp (q * (Real.log (d i) - Real.log dmin)))
          Filter.atBot
          (nhds (if d i = dmin then 1 else 0 : ℝ)) := by
    intro i hiS
    by_cases hi : d i = dmin
    · simp [hi]
    · have hlt : dmin < d i := lt_of_le_of_ne (hmin i hiS) (fun h => hi h.symm)
      have hgap : 0 < Real.log (d i) - Real.log dmin :=
        sub_pos.mpr (Real.log_lt_log hdmin_pos hlt)
      have hlin :
          Filter.Tendsto
            (fun q : ℝ => q * (Real.log (d i) - Real.log dmin))
            Filter.atBot Filter.atBot :=
        (Filter.tendsto_mul_const_atBot_of_pos hgap).2 (by
          simpa using (Filter.tendsto_id :
            Filter.Tendsto (fun q : ℝ => q) Filter.atBot Filter.atBot))
      have hexp :
          Filter.Tendsto
            (fun q : ℝ => Real.exp (q * (Real.log (d i) - Real.log dmin)))
            Filter.atBot (nhds 0) := by
        simpa [Function.comp_def] using Real.tendsto_exp_atBot.comp hlin
      simpa [hi] using hexp
  have hsum :
      Filter.Tendsto
        (fun q : ℝ =>
          Finset.sum S fun i => Real.exp (q * (Real.log (d i) - Real.log dmin)))
        Filter.atBot
        (nhds (Finset.sum S fun i => if d i = dmin then 1 else 0 : ℝ)) :=
    tendsto_finset_sum S hterm
  have hcount :
      (Finset.sum S fun i => if d i = dmin then 1 else 0 : ℝ) =
        xi_time_part9ze_negative_zero_temperature_freezing_minimizerCard S d dmin := by
    unfold xi_time_part9ze_negative_zero_temperature_freezing_minimizerCard
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    simp only [Nat.cast_one, Finset.sum_filter]
  refine Filter.Tendsto.congr' ?_ (hcount ▸ hsum)
  exact Filter.Eventually.of_forall fun q =>
    (xi_time_part9ze_negative_zero_temperature_freezing_normalized_eq_sum S d dmin q).symm

lemma xi_time_part9ze_negative_zero_temperature_freezing_freeEnergy_tendsto
    {ι : Type} [DecidableEq ι] (S : Finset ι) (d : ι → ℝ) (dmin : ℝ)
    (hS : S.Nonempty) (hpos : ∀ i ∈ S, 0 < d i) (hmin : ∀ i ∈ S, dmin ≤ d i)
    (hhit : ∃ i ∈ S, d i = dmin) :
    Filter.Tendsto
      (fun q : ℝ =>
        (1 / q) * Real.log
          (xi_time_part9ze_negative_zero_temperature_freezing_partition S d q) -
          Real.log dmin)
      Filter.atBot (nhds 0) := by
  have hnorm :=
    xi_time_part9ze_negative_zero_temperature_freezing_normalized_tendsto
      S d dmin hpos hmin hhit
  have hcount_pos :=
    xi_time_part9ze_negative_zero_temperature_freezing_minimizerCard_pos
      (S := S) (d := d) (dmin := dmin) hhit
  have hlog :
      Filter.Tendsto
        (fun q : ℝ =>
          Real.log (xi_time_part9ze_negative_zero_temperature_freezing_normalized S d dmin q))
        Filter.atBot
        (nhds
          (Real.log
            (xi_time_part9ze_negative_zero_temperature_freezing_minimizerCard S d dmin))) :=
    (Real.continuousAt_log hcount_pos.ne').tendsto.comp hnorm
  have hprod :
      Filter.Tendsto
        (fun q : ℝ =>
          q⁻¹ *
            Real.log (xi_time_part9ze_negative_zero_temperature_freezing_normalized S d dmin q))
        Filter.atBot (nhds 0) := by
    simpa using (tendsto_inv_atBot_zero.mul hlog)
  refine Filter.Tendsto.congr' ?_ hprod
  refine Filter.eventually_atBot.2 ⟨(-1 : ℝ), ?_⟩
  intro q hq
  have hqne : q ≠ 0 := by linarith
  have hnorm_pos :
      xi_time_part9ze_negative_zero_temperature_freezing_normalized S d dmin q ≠ 0 :=
    (xi_time_part9ze_negative_zero_temperature_freezing_normalized_pos
      (S := S) (d := d) (dmin := dmin) (q := q) hS).ne'
  exact (calc
    (1 / q) *
          Real.log (xi_time_part9ze_negative_zero_temperature_freezing_partition S d q) -
        Real.log dmin
        = (1 / q) *
            (Real.log (Real.exp (q * Real.log dmin)) +
              Real.log
                (xi_time_part9ze_negative_zero_temperature_freezing_normalized S d dmin q)) -
            Real.log dmin := by
          rw [xi_time_part9ze_negative_zero_temperature_freezing_partition_eq_exp_mul_normalized,
            Real.log_mul (Real.exp_ne_zero _) hnorm_pos]
    _ = (1 / q) *
            (q * Real.log dmin +
              Real.log
                (xi_time_part9ze_negative_zero_temperature_freezing_normalized S d dmin q)) -
            Real.log dmin := by
          rw [Real.log_exp]
    _ =
        q⁻¹ *
          Real.log (xi_time_part9ze_negative_zero_temperature_freezing_normalized S d dmin q) := by
          field_simp [hqne]
          ring).symm

/-- Paper label: `thm:xi-time-part9ze-negative-zero-temperature-freezing`. -/
theorem paper_xi_time_part9ze_negative_zero_temperature_freezing
    {ι : Type} [DecidableEq ι] (S : Finset ι) (d : ι → ℝ) (dmin : ℝ)
    (hS : S.Nonempty) (hpos : ∀ i ∈ S, 0 < d i) (hmin : ∀ i ∈ S, dmin ≤ d i)
    (hhit : ∃ i ∈ S, d i = dmin) :
    (∀ ε > 0, ∃ Q : ℝ, ∀ q ≤ Q,
      |(1 / q) * Real.log (Finset.sum S (fun i => Real.exp (q * Real.log (d i)))) -
          Real.log dmin| < ε) ∧
      (∀ ε > 0, ∃ Q : ℝ, ∀ q ≤ Q,
        |Real.exp (-q * Real.log dmin) *
              Finset.sum S (fun i => Real.exp (q * Real.log (d i))) -
            ((S.filter fun i => d i = dmin).card : ℝ)| < ε) := by
  constructor
  · intro ε hε
    have ht :=
      xi_time_part9ze_negative_zero_temperature_freezing_freeEnergy_tendsto
        S d dmin hS hpos hmin hhit
    have hdist := (Metric.tendsto_nhds.mp ht) ε hε
    rcases Filter.eventually_atBot.mp hdist with ⟨Q, hQ⟩
    refine ⟨Q, ?_⟩
    intro q hq
    have := hQ q hq
    simpa [xi_time_part9ze_negative_zero_temperature_freezing_partition, Real.dist_eq] using this
  · intro ε hε
    have ht :=
      xi_time_part9ze_negative_zero_temperature_freezing_normalized_tendsto
        S d dmin hpos hmin hhit
    have hdist := (Metric.tendsto_nhds.mp ht) ε hε
    rcases Filter.eventually_atBot.mp hdist with ⟨Q, hQ⟩
    refine ⟨Q, ?_⟩
    intro q hq
    have := hQ q hq
    simpa [xi_time_part9ze_negative_zero_temperature_freezing_normalized,
      xi_time_part9ze_negative_zero_temperature_freezing_partition,
      xi_time_part9ze_negative_zero_temperature_freezing_minimizerCard,
      Real.dist_eq] using this

end Omega.Zeta
