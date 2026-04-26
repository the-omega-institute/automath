import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.SyncKernelRealInput

noncomputable section

/-- The vertical spacing attached to a `q`-fold phase lift over the Perron scale `lam`. -/
def finite_rh_beat_irrational_log_step (q : ℕ) (lam : ℝ) : ℝ :=
  2 * Real.pi / ((q : ℝ) * Real.log lam)

/-- A single vertical arithmetic comb based at `offset` with step `step`. -/
def finite_rh_beat_irrational_log_comb (offset step : ℝ) : Set ℝ :=
  {t | ∃ n : ℤ, t = offset + n * step}

/-- A finite union of vertical arithmetic combs sharing the same step. -/
def finite_rh_beat_irrational_log_comb_union {ι : Type*} (offset : ι → ℝ) (step : ℝ) : Set ℝ :=
  {t | ∃ i, t ∈ finite_rh_beat_irrational_log_comb (offset i) step}

private theorem finite_rh_beat_irrational_log_comb_union_add_zsmul
    {ι : Type*} (offset : ι → ℝ) (step : ℝ) (k : ℤ) {t : ℝ}
    (ht : t ∈ finite_rh_beat_irrational_log_comb_union offset step) :
    t + k * step ∈ finite_rh_beat_irrational_log_comb_union offset step := by
  rcases ht with ⟨i, n, rfl⟩
  refine ⟨i, n + k, ?_⟩
  rw [Int.cast_add]
  ring

/-- Paper label: `prop:finite-rh-beat-irrational-log`.
If the logarithmic scales are rationally related, then the two finite comb unions share a common
vertical period, so their union remains periodic and cannot produce an aperiodic beat pattern. -/
theorem paper_finite_rh_beat_irrational_log
    {ιa ιb : Type*} [Fintype ιa] [Fintype ιb]
    (lamA lamB : ℝ) (qa qb p q : ℕ)
    (offsetA : ιa → ℝ) (offsetB : ιb → ℝ)
    (hlamA : 1 < lamA) (hlamB : 1 < lamB)
    (hqa : 0 < qa) (hqb : 0 < qb) (hp : 0 < p) (hq : 0 < q)
    (hrat : Real.log lamA / Real.log lamB = (p : ℝ) / q) :
    let Δa := finite_rh_beat_irrational_log_step qa lamA
    let Δb := finite_rh_beat_irrational_log_step qb lamB
    let SA := finite_rh_beat_irrational_log_comb_union offsetA Δa
    let SB := finite_rh_beat_irrational_log_comb_union offsetB Δb
    let Δ := 2 * Real.pi * q / Real.log lamB
    (∀ t, t ∈ SA → t + Δ ∈ SA) ∧
      (∀ t, t ∈ SB → t + Δ ∈ SB) ∧
      (∀ t, t ∈ SA ∪ SB → t + Δ ∈ SA ∪ SB) := by
  dsimp
  have hlogb_pos : 0 < Real.log lamB := Real.log_pos hlamB
  have hloga_pos : 0 < Real.log lamA := Real.log_pos hlamA
  have hlogb_ne : Real.log lamB ≠ 0 := hlogb_pos.ne'
  have hloga_ne : Real.log lamA ≠ 0 := hloga_pos.ne'
  have hq_ne : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  have hqa_ne : (qa : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hqa)
  have hqb_ne : (qb : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hqb)
  have hrat' : Real.log lamA = ((p : ℝ) / q) * Real.log lamB := by
    exact (div_eq_iff hlogb_ne).mp hrat
  have hcross : (q : ℝ) * Real.log lamA = (p : ℝ) * Real.log lamB := by
    calc
      (q : ℝ) * Real.log lamA = (q : ℝ) * (((p : ℝ) / q) * Real.log lamB) := by rw [hrat']
      _ = (p : ℝ) * Real.log lamB := by field_simp [hq_ne]
  have hΔa :
      2 * Real.pi * q / Real.log lamB =
        ((qa * p : ℕ) : ℝ) * finite_rh_beat_irrational_log_step qa lamA := by
    calc
      2 * Real.pi * q / Real.log lamB = 2 * Real.pi * p / Real.log lamA := by
        field_simp [hloga_ne, hlogb_ne]
        linarith [hcross]
      _ = ((qa * p : ℕ) : ℝ) * finite_rh_beat_irrational_log_step qa lamA := by
        unfold finite_rh_beat_irrational_log_step
        field_simp [hqa_ne, hloga_ne]
        norm_num [Nat.cast_mul]
        ring
  have hΔb :
      2 * Real.pi * q / Real.log lamB =
        ((qb * q : ℕ) : ℝ) * finite_rh_beat_irrational_log_step qb lamB := by
    unfold finite_rh_beat_irrational_log_step
    field_simp [hqb_ne, hlogb_ne]
    norm_num [Nat.cast_mul]
    ring
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    have hshift :=
      finite_rh_beat_irrational_log_comb_union_add_zsmul offsetA
        (finite_rh_beat_irrational_log_step qa lamA) (Int.ofNat (qa * p)) ht
    simpa [hΔa] using hshift
  · intro t ht
    have hshift :=
      finite_rh_beat_irrational_log_comb_union_add_zsmul offsetB
        (finite_rh_beat_irrational_log_step qb lamB) (Int.ofNat (qb * q)) ht
    simpa [hΔb] using hshift
  · intro t ht
    rcases ht with ht | ht
    · exact Or.inl ((by
        have hshift :=
          finite_rh_beat_irrational_log_comb_union_add_zsmul offsetA
            (finite_rh_beat_irrational_log_step qa lamA) (Int.ofNat (qa * p)) ht
        simpa [hΔa] using hshift) : t + 2 * Real.pi * q / Real.log lamB ∈
          finite_rh_beat_irrational_log_comb_union offsetA
            (finite_rh_beat_irrational_log_step qa lamA))
    · exact Or.inr ((by
        have hshift :=
          finite_rh_beat_irrational_log_comb_union_add_zsmul offsetB
            (finite_rh_beat_irrational_log_step qb lamB) (Int.ofNat (qb * q)) ht
        simpa [hΔb] using hshift) : t + 2 * Real.pi * q / Real.log lamB ∈
          finite_rh_beat_irrational_log_comb_union offsetB
            (finite_rh_beat_irrational_log_step qb lamB))

end

end Omega.SyncKernelRealInput
