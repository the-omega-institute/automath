import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic

namespace Omega.POM

lemma pom_anom_signature_tower_sympower_complexity_separation_eventual_pow_bound
    (B r : ℕ) :
    ∃ q0 : ℕ, ∀ q ≥ q0, B * Nat.choose (q + r) r + 2 < 2 ^ (q + 1) := by
  let C : ℕ := B * (r + 1) ^ r
  let A : ℕ := C + 2
  have hlim :
      Filter.Tendsto (fun q : ℕ => (A : ℝ) * ((q : ℝ) ^ r / (2 : ℝ) ^ q))
        Filter.atTop (nhds 0) := by
    simpa using
      (tendsto_pow_const_div_const_pow_of_one_lt r
        (by norm_num : (1 : ℝ) < 2)).const_mul (A : ℝ)
  have hevent :
      ∀ᶠ q : ℕ in Filter.atTop,
        (A : ℝ) * ((q : ℝ) ^ r / (2 : ℝ) ^ q) < 2 := by
    exact hlim.eventually (isOpen_Iio.mem_nhds (by norm_num : (0 : ℝ) < 2))
  rcases Filter.eventually_atTop.mp hevent with ⟨q1, hq1⟩
  refine ⟨max 1 q1, ?_⟩
  intro q hq
  have hq_ge_one : 1 ≤ q := le_trans (Nat.le_max_left 1 q1) hq
  have hq_ge_q1 : q1 ≤ q := le_trans (Nat.le_max_right 1 q1) hq
  have hratio : (A : ℝ) * ((q : ℝ) ^ r / (2 : ℝ) ^ q) < 2 := hq1 q hq_ge_q1
  have hden_pos : (0 : ℝ) < (2 : ℝ) ^ q := pow_pos (by norm_num) q
  have hA_real : (A : ℝ) * (q : ℝ) ^ r < 2 * (2 : ℝ) ^ q := by
    have hratio' : ((A : ℝ) * (q : ℝ) ^ r) / (2 : ℝ) ^ q < 2 := by
      simpa [mul_div_assoc] using hratio
    exact (div_lt_iff₀ hden_pos).mp hratio'
  have hA_nat : A * q ^ r < 2 ^ (q + 1) := by
    have hA_real' : ((A * q ^ r : ℕ) : ℝ) < ((2 ^ (q + 1) : ℕ) : ℝ) := by
      simpa [Nat.cast_mul, Nat.cast_pow, pow_succ, mul_comm, mul_left_comm, mul_assoc]
        using hA_real
    exact_mod_cast hA_real'
  have hchoose_le : Nat.choose (q + r) r ≤ (q + r) ^ r :=
    Nat.choose_le_pow (q + r) r
  have hqr_base : q + r ≤ (r + 1) * q := by
    nlinarith [Nat.mul_le_mul_left r hq_ge_one]
  have hqr : (q + r) ^ r ≤ ((r + 1) * q) ^ r :=
    Nat.pow_le_pow_left hqr_base r
  have hchoose_bound : B * Nat.choose (q + r) r ≤ C * q ^ r := by
    calc
      B * Nat.choose (q + r) r ≤ B * (q + r) ^ r :=
        Nat.mul_le_mul_left B hchoose_le
      _ ≤ B * (((r + 1) * q) ^ r) := Nat.mul_le_mul_left B hqr
      _ = C * q ^ r := by
        simp [C, Nat.mul_pow, Nat.mul_assoc]
  have hqpow_one : 1 ≤ q ^ r := Nat.succ_le_of_lt (pow_pos (by omega : 0 < q) r)
  have htwo_bound : 2 ≤ 2 * q ^ r := by
    simpa using Nat.mul_le_mul_left 2 hqpow_one
  have htotal_bound : B * Nat.choose (q + r) r + 2 ≤ A * q ^ r := by
    calc
      B * Nat.choose (q + r) r + 2 ≤ C * q ^ r + 2 * q ^ r :=
        Nat.add_le_add hchoose_bound htwo_bound
      _ = A * q ^ r := by
        simp [A]
        ring
  exact lt_of_le_of_lt htotal_bound hA_nat

/-- Paper label: `cor:pom-anom-signature-tower-sympower-complexity-separation`. -/
theorem paper_pom_anom_signature_tower_sympower_complexity_separation
    (g r : ℕ) (hg : 2 ≤ g) :
    ∀ B : ℕ, ∃ q0 : ℕ, ∀ q ≥ q0,
      B * Nat.choose (q + r) r < g ^ (q + 1) - 1 := by
  intro B
  rcases pom_anom_signature_tower_sympower_complexity_separation_eventual_pow_bound B r with
    ⟨q0, hq0⟩
  refine ⟨q0, ?_⟩
  intro q hq
  have htwo : B * Nat.choose (q + r) r + 2 < 2 ^ (q + 1) := hq0 q hq
  have htwo_le_g : 2 ^ (q + 1) ≤ g ^ (q + 1) := Nat.pow_le_pow_left hg (q + 1)
  have hgrowth : B * Nat.choose (q + r) r + 2 < g ^ (q + 1) :=
    lt_of_lt_of_le htwo htwo_le_g
  omega

end Omega.POM
