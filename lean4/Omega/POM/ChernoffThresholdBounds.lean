import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.Folding.MomentSum

open scoped BigOperators

namespace Omega.POM

/-- The fold outputs whose fiber multiplicity exceeds the exponential threshold `exp (α m)`. -/
noncomputable def chernoffThresholdSet (m : ℕ) (α : ℝ) : Finset (Omega.X m) :=
  Finset.univ.filter fun x => α * (m : ℝ) ≤ Real.log (Omega.X.fiberMultiplicity x : ℝ)

/-- The pushforward mass of an event under the uniform microstate law. -/
noncomputable def chernoffThresholdPushforwardMass (m : ℕ) (α : ℝ) : ℝ :=
  Finset.sum (chernoffThresholdSet m α) fun x =>
    (Omega.X.fiberMultiplicity x : ℝ) / (2 : ℝ) ^ m

private lemma threshold_count_pointwise (m q : ℕ) (α : ℝ) {x : Omega.X m}
    (hx : x ∈ chernoffThresholdSet m α) :
    1 ≤ Real.exp (-(q : ℝ) * α * m) * (Omega.X.fiberMultiplicity x : ℝ) ^ q := by
  have hq_nonneg : 0 ≤ (q : ℝ) := by positivity
  have hd_pos : 0 < (Omega.X.fiberMultiplicity x : ℝ) := by
    exact_mod_cast Omega.X.fiberMultiplicity_pos x
  have hxlog : α * (m : ℝ) ≤ Real.log (Omega.X.fiberMultiplicity x : ℝ) :=
    (Finset.mem_filter.mp hx).2
  have hmul :
      (q : ℝ) * (α * (m : ℝ)) ≤ (q : ℝ) * Real.log (Omega.X.fiberMultiplicity x : ℝ) :=
    mul_le_mul_of_nonneg_left hxlog hq_nonneg
  have hexp :
      Real.exp ((q : ℝ) * α * m) ≤ (Omega.X.fiberMultiplicity x : ℝ) ^ q := by
    have hlogineq :
        (q : ℝ) * α * m ≤ Real.log ((Omega.X.fiberMultiplicity x : ℝ) ^ q) := by
      simpa [mul_assoc, mul_left_comm, mul_comm, Real.log_pow] using hmul
    have hpow_pos : 0 < (Omega.X.fiberMultiplicity x : ℝ) ^ q := pow_pos hd_pos q
    calc
      Real.exp ((q : ℝ) * α * m) ≤ Real.exp (Real.log ((Omega.X.fiberMultiplicity x : ℝ) ^ q)) :=
        Real.exp_le_exp.mpr hlogineq
      _ = (Omega.X.fiberMultiplicity x : ℝ) ^ q := by rw [Real.exp_log hpow_pos]
  have hdiv :
      1 ≤ (Omega.X.fiberMultiplicity x : ℝ) ^ q / Real.exp ((q : ℝ) * α * m) :=
    (one_le_div₀ (Real.exp_pos _)).2 hexp
  simpa [div_eq_mul_inv, Real.exp_neg, mul_assoc, mul_left_comm, mul_comm] using hdiv

private lemma threshold_pushforward_pointwise (m q : ℕ) (α : ℝ) {x : Omega.X m}
    (hx : x ∈ chernoffThresholdSet m α) :
    (Omega.X.fiberMultiplicity x : ℝ) / (2 : ℝ) ^ m ≤
      Real.exp (-(q : ℝ) * α * m) *
        ((Omega.X.fiberMultiplicity x : ℝ) ^ (q + 1) / (2 : ℝ) ^ m) := by
  have hd_pos : 0 < (Omega.X.fiberMultiplicity x : ℝ) := by
    exact_mod_cast Omega.X.fiberMultiplicity_pos x
  have hq_nonneg : 0 ≤ (q : ℝ) := by positivity
  have hxlog : α * (m : ℝ) ≤ Real.log (Omega.X.fiberMultiplicity x : ℝ) :=
    (Finset.mem_filter.mp hx).2
  have hmul :
      (q : ℝ) * (α * (m : ℝ)) ≤ (q : ℝ) * Real.log (Omega.X.fiberMultiplicity x : ℝ) :=
    mul_le_mul_of_nonneg_left hxlog hq_nonneg
  have hexp :
      Real.exp ((q : ℝ) * α * m) ≤ (Omega.X.fiberMultiplicity x : ℝ) ^ q := by
    have hlogineq :
        (q : ℝ) * α * m ≤ Real.log ((Omega.X.fiberMultiplicity x : ℝ) ^ q) := by
      simpa [mul_assoc, mul_left_comm, mul_comm, Real.log_pow] using hmul
    have hpow_pos : 0 < (Omega.X.fiberMultiplicity x : ℝ) ^ q := pow_pos hd_pos q
    calc
      Real.exp ((q : ℝ) * α * m) ≤ Real.exp (Real.log ((Omega.X.fiberMultiplicity x : ℝ) ^ q)) :=
        Real.exp_le_exp.mpr hlogineq
      _ = (Omega.X.fiberMultiplicity x : ℝ) ^ q := by rw [Real.exp_log hpow_pos]
  have hmain :
      (Omega.X.fiberMultiplicity x : ℝ) ≤
        Real.exp (-(q : ℝ) * α * m) * (Omega.X.fiberMultiplicity x : ℝ) ^ (q + 1) := by
    have hmul' :
        (Omega.X.fiberMultiplicity x : ℝ) * Real.exp ((q : ℝ) * α * m) ≤
          (Omega.X.fiberMultiplicity x : ℝ) * (Omega.X.fiberMultiplicity x : ℝ) ^ q :=
      mul_le_mul_of_nonneg_left hexp hd_pos.le
    have hpow_succ :
        (Omega.X.fiberMultiplicity x : ℝ) * (Omega.X.fiberMultiplicity x : ℝ) ^ q =
          (Omega.X.fiberMultiplicity x : ℝ) ^ (q + 1) := by
      rw [pow_succ']
    have hdiv :
        (Omega.X.fiberMultiplicity x : ℝ) ≤
          (Omega.X.fiberMultiplicity x : ℝ) ^ (q + 1) / Real.exp ((q : ℝ) * α * m) := by
      exact (le_div_iff₀ (Real.exp_pos _)).2 <| by
        simpa [hpow_succ, mul_comm, mul_left_comm, mul_assoc] using hmul'
    simpa [div_eq_mul_inv, Real.exp_neg, mul_assoc, mul_left_comm, mul_comm] using hdiv
  have hmaindiv :
      (Omega.X.fiberMultiplicity x : ℝ) / (2 : ℝ) ^ m ≤
        (Real.exp (-(q : ℝ) * α * m) * (Omega.X.fiberMultiplicity x : ℝ) ^ (q + 1)) /
          (2 : ℝ) ^ m :=
    (div_le_div_iff_of_pos_right (show 0 < (2 : ℝ) ^ m by positivity)).2 hmain
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmaindiv

/-- Paper label: `prop:pom-chernoff-threshold-bounds`.
Summing the pointwise threshold inequality over the high-multiplicity set gives the counting bound,
and weighting by `d(x) / 2^m` gives the pushforward bound. -/
theorem paper_pom_chernoff_threshold_bounds (m q : ℕ) (_hq : 1 ≤ q) (α : ℝ) :
    ((chernoffThresholdSet m α).card : ℝ) ≤
      Real.exp (-(q : ℝ) * α * m) * (Omega.momentSum q m : ℝ) ∧
    chernoffThresholdPushforwardMass m α ≤
      Real.exp (-(q : ℝ) * α * m) * (Omega.momentSum (q + 1) m : ℝ) / (2 : ℝ) ^ m := by
  let A := chernoffThresholdSet m α
  have hcount_sum :
      Finset.sum A (fun _ => (1 : ℝ)) ≤
        Finset.sum A (fun x => Real.exp (-(q : ℝ) * α * m) * (Omega.X.fiberMultiplicity x : ℝ) ^ q) := by
    exact Finset.sum_le_sum fun x hx => threshold_count_pointwise m q α (by simpa [A] using hx)
  have hcount_univ :
      Finset.sum A (fun x => Real.exp (-(q : ℝ) * α * m) * (Omega.X.fiberMultiplicity x : ℝ) ^ q) ≤
        Finset.univ.sum (fun x : Omega.X m =>
          Real.exp (-(q : ℝ) * α * m) * (Omega.X.fiberMultiplicity x : ℝ) ^ q) := by
    exact Finset.sum_le_univ_sum_of_nonneg fun _ => by positivity
  have hcount_eval :
      Finset.univ.sum (fun x : Omega.X m =>
          Real.exp (-(q : ℝ) * α * m) * (Omega.X.fiberMultiplicity x : ℝ) ^ q) =
        Real.exp (-(q : ℝ) * α * m) * (Omega.momentSum q m : ℝ) := by
    rw [show Finset.univ.sum (fun x : Omega.X m =>
        Real.exp (-(q : ℝ) * α * m) * (Omega.X.fiberMultiplicity x : ℝ) ^ q) =
          Real.exp (-(q : ℝ) * α * m) *
            Finset.univ.sum (fun x : Omega.X m => (Omega.X.fiberMultiplicity x : ℝ) ^ q) by
          rw [Finset.mul_sum]]
    simp [Omega.momentSum]
  have hcount :
      ((A.card : ℕ) : ℝ) ≤ Real.exp (-(q : ℝ) * α * m) * (Omega.momentSum q m : ℝ) := by
    calc
      ((A.card : ℕ) : ℝ) = Finset.sum A (fun _ => (1 : ℝ)) := by
        rw [Finset.card_eq_sum_ones]
        norm_num
      _ ≤ Finset.sum A (fun x => Real.exp (-(q : ℝ) * α * m) * (Omega.X.fiberMultiplicity x : ℝ) ^ q) :=
        hcount_sum
      _ ≤ Finset.univ.sum (fun x : Omega.X m =>
          Real.exp (-(q : ℝ) * α * m) * (Omega.X.fiberMultiplicity x : ℝ) ^ q) :=
        hcount_univ
      _ = Real.exp (-(q : ℝ) * α * m) * (Omega.momentSum q m : ℝ) := hcount_eval
  have hpush_sum :
      chernoffThresholdPushforwardMass m α ≤
        Finset.sum A (fun x =>
          Real.exp (-(q : ℝ) * α * m) *
            ((Omega.X.fiberMultiplicity x : ℝ) ^ (q + 1) / (2 : ℝ) ^ m)) := by
    unfold chernoffThresholdPushforwardMass
    exact Finset.sum_le_sum fun x hx => threshold_pushforward_pointwise m q α (by simpa [A] using hx)
  have hpush_univ :
      Finset.sum A (fun x =>
          Real.exp (-(q : ℝ) * α * m) *
            ((Omega.X.fiberMultiplicity x : ℝ) ^ (q + 1) / (2 : ℝ) ^ m)) ≤
        Finset.univ.sum (fun x : Omega.X m =>
          Real.exp (-(q : ℝ) * α * m) *
            ((Omega.X.fiberMultiplicity x : ℝ) ^ (q + 1) / (2 : ℝ) ^ m)) := by
    exact Finset.sum_le_univ_sum_of_nonneg fun _ => by positivity
  have hpush_eval :
      Finset.univ.sum (fun x : Omega.X m =>
          Real.exp (-(q : ℝ) * α * m) *
            ((Omega.X.fiberMultiplicity x : ℝ) ^ (q + 1) / (2 : ℝ) ^ m)) =
        Real.exp (-(q : ℝ) * α * m) * (Omega.momentSum (q + 1) m : ℝ) / (2 : ℝ) ^ m := by
    rw [show Finset.univ.sum (fun x : Omega.X m =>
        Real.exp (-(q : ℝ) * α * m) *
          ((Omega.X.fiberMultiplicity x : ℝ) ^ (q + 1) / (2 : ℝ) ^ m)) =
          Real.exp (-(q : ℝ) * α * m) *
            Finset.univ.sum (fun x : Omega.X m =>
              ((Omega.X.fiberMultiplicity x : ℝ) ^ (q + 1) / (2 : ℝ) ^ m)) by
          rw [Finset.mul_sum]]
    rw [show Finset.univ.sum (fun x : Omega.X m =>
        ((Omega.X.fiberMultiplicity x : ℝ) ^ (q + 1) / (2 : ℝ) ^ m)) =
        Finset.univ.sum (fun x : Omega.X m => (Omega.X.fiberMultiplicity x : ℝ) ^ (q + 1)) /
          (2 : ℝ) ^ m by
          rw [Finset.sum_div]]
    simp [Omega.momentSum, mul_left_comm, mul_comm, div_eq_mul_inv]
  have hpush :
      chernoffThresholdPushforwardMass m α ≤
        Real.exp (-(q : ℝ) * α * m) * (Omega.momentSum (q + 1) m : ℝ) / (2 : ℝ) ^ m := by
    calc
      chernoffThresholdPushforwardMass m α ≤
          Finset.sum A (fun x =>
            Real.exp (-(q : ℝ) * α * m) *
              ((Omega.X.fiberMultiplicity x : ℝ) ^ (q + 1) / (2 : ℝ) ^ m)) := hpush_sum
      _ ≤ Finset.univ.sum (fun x : Omega.X m =>
          Real.exp (-(q : ℝ) * α * m) *
            ((Omega.X.fiberMultiplicity x : ℝ) ^ (q + 1) / (2 : ℝ) ^ m)) := hpush_univ
      _ = Real.exp (-(q : ℝ) * α * m) * (Omega.momentSum (q + 1) m : ℝ) / (2 : ℝ) ^ m :=
        hpush_eval
  exact ⟨by simpa [A] using hcount, hpush⟩

end Omega.POM
