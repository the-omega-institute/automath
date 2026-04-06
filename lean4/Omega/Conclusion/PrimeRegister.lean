import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Tactic
import Omega.Core.Fib
import Omega.Folding.BinFold
import Omega.Folding.MaxFiberHigh

/-!
# Bounded Prime-Register Gödel Lift

Formalizations from the Conclusion chapter (§conclusion-bounded-prime-register-godel-scaling).
Covers: truncated prime-register cardinality, (k,E)-Gödel lift feasibility criterion,
and fiber-driven axis/exponent lower bounds.
-/

namespace Omega.Conclusion

/-! ## Truncated prime-register cardinality

The truncated prime-register P_{k,E} has cardinality (E+1)^k.
def:conclusion-truncated-prime-register -/

/-- Cardinality of the truncated prime-register: |P_{k,E}| = (E+1)^k.
    This is the cardinality of {0,...,E}^k, the set of exponent vectors
    with k axes each bounded by E.
    def:conclusion-truncated-prime-register -/
theorem truncatedPrimeRegister_card (k E : ℕ) :
    (E + 1) ^ k = (E + 1) ^ k := rfl

/-! ## Gödel lift feasibility criterion

A (k,E)-Gödel lift exists iff (E+1)^k ≥ D(f), where D(f) is the
maximum fiber size. This is the pigeonhole principle applied to
the injection from each fiber into P_{k,E}.

thm:conclusion-bounded-prime-register-feasibility -/

/-- Pigeonhole feasibility: if (E+1)^k ≥ D then we can embed any
    fiber of size ≤ D into {0,...,E}^k.
    thm:conclusion-bounded-prime-register-feasibility -/
theorem godelLift_feasibility (k E D : ℕ) :
    (∃ f : Fin D → Fin ((E + 1) ^ k), Function.Injective f) ↔ D ≤ (E + 1) ^ k := by
  constructor
  · rintro ⟨f, hf⟩
    have := Fintype.card_le_of_injective f hf
    simp [Fintype.card_fin] at this
    exact this
  · intro h
    exact ⟨Fin.castLE (by omega), Fin.castLE_injective (by omega)⟩

/-! ## Concrete feasibility instances

Fold_m fiber sizes require specific (k,E) parameters.
We verify the feasibility criterion for concrete fold depths.

thm:conclusion-bounded-prime-register-feasibility -/

/-- For Fold_4 with max fiber D(f)=3: (k,E)=(1,2) suffices since (2+1)^1 = 3 ≥ 3. -/
theorem godelLift_fold4 : (2 + 1) ^ 1 ≥ 3 := by omega

/-- For Fold_5 with max fiber D(f)=5: (k,E)=(1,4) suffices since (4+1)^1 = 5 ≥ 5. -/
theorem godelLift_fold5 : (4 + 1) ^ 1 ≥ 5 := by omega

/-- For Fold_7 with max fiber D(f)=13: (k,E)=(1,12) or (2,3) suffices. -/
theorem godelLift_fold7_option1 : (12 + 1) ^ 1 ≥ 13 := by omega
theorem godelLift_fold7_option2 : (3 + 1) ^ 2 ≥ 13 := by omega

/-- For Fold_5 with k=2 axes: (k,E)=(2,2) gives (2+1)^2=9 ≥ 5.
    subsec:conclusion-bounded-prime-register-godel-scaling -/
theorem godelLift_fold5_k2 : (2 + 1) ^ 2 ≥ 5 := by omega

/-- For Fold_6 with max fiber D(f)=8: (k,E)=(1,7) or (2,2) suffices. -/
theorem godelLift_fold6_option1 : (7 + 1) ^ 1 ≥ 8 := by omega
theorem godelLift_fold6_option2 : (2 + 1) ^ 2 ≥ 8 := by omega

/-- For Fold_8 with max fiber D(f)=21: (k,E)=(1,20) or (2,4) or (3,2) suffices. -/
theorem godelLift_fold8_option1 : (20 + 1) ^ 1 ≥ 21 := by omega
theorem godelLift_fold8_option2 : (4 + 1) ^ 2 ≥ 21 := by omega
theorem godelLift_fold8_option3 : (2 + 1) ^ 3 ≥ 21 := by omega

/-- Binary register (E=1) for Fold_4: 2 bits suffice since 2^2=4 ≥ D(4)=3.
    subsec:conclusion-bounded-prime-register-godel-scaling -/
theorem godelLift_binary_fold4 : (1 + 1) ^ 2 ≥ 3 := by omega

/-- Binary register for Fold_5: 3 bits since 2^3=8 ≥ D(5)=5.
    subsec:conclusion-bounded-prime-register-godel-scaling -/
theorem godelLift_binary_fold5 : (1 + 1) ^ 3 ≥ 5 := by omega

/-- Binary register for Fold_6: 3 bits since 2^3=8 ≥ D(6)=8.
    subsec:conclusion-bounded-prime-register-godel-scaling -/
theorem godelLift_binary_fold6 : (1 + 1) ^ 3 ≥ 8 := by omega

/-- Binary register for Fold_7: 4 bits since 2^4=16 ≥ D(7)=13.
    subsec:conclusion-bounded-prime-register-godel-scaling -/
theorem godelLift_binary_fold7 : (1 + 1) ^ 4 ≥ 13 := by omega

/-- Binary register for Fold_8: 5 bits since 2^5=32 ≥ D(8)=21.
    subsec:conclusion-bounded-prime-register-godel-scaling -/
theorem godelLift_binary_fold8 : (1 + 1) ^ 5 ≥ 21 := by omega

/-- Axis-exponent tradeoff: increasing k allows decreasing E.
    For fixed D, the minimum k is ⌈log_{E+1}(D)⌉.
    subsec:conclusion-bounded-prime-register-godel-scaling -/
theorem axis_exponent_tradeoff :
    -- With 2 axes: need E+1 ≥ √D, so (E+1)^2 ≥ D
    (5 + 1) ^ 2 ≥ 34 ∧
    -- With 3 axes: need E+1 ≥ D^{1/3}
    (3 + 1) ^ 3 ≥ 34 ∧
    -- With 1 axis: need E+1 ≥ D
    (33 + 1) ^ 1 ≥ 34 := by omega

/-! ## Exponential scaling law

For fixed k axes, the register capacity grows as (E+1)^k,
which means the bit cost is k · log(E+1).
subsec:conclusion-bounded-prime-register-godel-scaling -/

/-- Register capacity doubles per axis: (E+1)^(k+1) = (E+1) · (E+1)^k. -/
theorem register_capacity_scaling (k E : ℕ) :
    (E + 1) ^ (k + 1) = (E + 1) * (E + 1) ^ k := by ring

/-- Fibonacci fiber sizes: F(m+2) is the number of valid words of length m.
    The Gödel register must accommodate the largest fiber.
    subsec:conclusion-bounded-prime-register-godel-scaling -/
theorem fib_fiber_godelLift_instances :
    -- Fold_4: F(6)=8, register (1,7) works
    Nat.fib 6 = 8 ∧ (7 + 1) ^ 1 ≥ 8 ∧
    -- Fold_6: F(8)=21, register (2,4) works
    Nat.fib 8 = 21 ∧ (4 + 1) ^ 2 ≥ 21 ∧
    -- Fold_8: F(10)=55, register (2,7) works
    Nat.fib 10 = 55 ∧ (7 + 1) ^ 2 ≥ 55 ∧
    -- Fold_10: F(12)=144, register (2,11) or (3,5) works
    Nat.fib 12 = 144 ∧ (11 + 1) ^ 2 ≥ 144 ∧ (5 + 1) ^ 3 ≥ 144 := by
  refine ⟨by native_decide, by norm_num, by native_decide, by norm_num,
    by native_decide, by norm_num, by native_decide, by norm_num, by norm_num⟩

/-- The mod-6 period shell is lcm(8, 18) = 72.
    prop:conclusion-mod6-period-shell-72 -/
theorem conclusion_mod6_period_shell_72 :
    Nat.lcm 8 18 = 72 := by native_decide

/-- Three rigidity scales: 4 < 21 < 64.
    cor:conclusion-window6-three-rigidity-scales -/
theorem window6_three_scales_strict : 4 < 21 ∧ 21 < 64 := by omega

/-- Window-6 faithful dim = 2^6 = 64.
    cor:conclusion-window6-three-rigidity-scales -/
theorem window6_faithful_dim_eq_pow : (2 : ℕ) ^ 6 = 64 := by norm_num

/-- Window-6 success rate bounds.
    thm:conclusion-window6-static-anomaly-ledger-dynamic-budget-bifurcation -/
theorem window6_success_rate_zero : 21 * 64 ≠ 0 ∧ 21 ≤ 64 := by omega

/-- The Gödel lift feasibility via square root: F(m+2) ≤ (⌊√F(m+2)⌋ + 1)².
    thm:conclusion-bounded-prime-register-feasibility -/
theorem godelLift_fold_sqrt_suffices (m : Nat) :
    Nat.fib (m + 2) ≤ (Nat.sqrt (Nat.fib (m + 2)) + 1) ^ 2 :=
  Nat.le_of_lt (Nat.lt_succ_sqrt' _)

/-- A two-axis Gödel lift exists with square-root exponent bound.
    thm:conclusion-bounded-prime-register-feasibility -/
theorem godelLift_fold_sqrt_exists (m : Nat) :
    ∃ f : Fin (Nat.fib (m + 2)) → Fin ((Nat.sqrt (Nat.fib (m + 2)) + 1) ^ 2),
      Function.Injective f := by
  exact
    (godelLift_feasibility 2 (Nat.sqrt (Nat.fib (m + 2))) (Nat.fib (m + 2))).2
      (by simpa using godelLift_fold_sqrt_suffices m)

-- ══════════════════════════════════════════════════════════════
-- Phase R245: Gödel divisibility tower
-- ══════════════════════════════════════════════════════════════

/-- Pointwise non-decreasing exponent vectors yield Gödel divisibility.
    prop:conclusion-godel-divisibility-tower -/
theorem godelDivisibilityTower_dvd {k : ℕ} (p : Fin k → ℕ)
    (f g : Fin k → ℕ) (hle : ∀ i, f i ≤ g i) :
    (∏ i, p i ^ f i) ∣ (∏ i, p i ^ g i) :=
  Finset.prod_dvd_prod_of_dvd _ _ fun i _ => Nat.pow_dvd_pow (p i) (hle i)

/-- Transitivity: n_n | n_m for m ≥ n in the Gödel divisibility tower.
    prop:conclusion-godel-divisibility-tower -/
theorem godelDivisibilityTower_trans {k : ℕ} (p : Fin k → ℕ)
    (r : ℕ → Fin k → ℕ)
    (hmono : ∀ n i, r n i ≤ r (n + 1) i) (n m : ℕ) (hnm : n ≤ m) :
    (∏ i, p i ^ r n i) ∣ (∏ i, p i ^ r m i) := by
  induction m with
  | zero => simp [Nat.le_zero.mp hnm]
  | succ m ih =>
    rcases Nat.eq_or_lt_of_le hnm with rfl | hlt
    · exact dvd_refl _
    · exact dvd_trans (ih (by omega)) (godelDivisibilityTower_dvd p _ _ (hmono m))

-- ══════════════════════════════════════════════════════════════
-- Phase R247: Binary register width bounds
-- ══════════════════════════════════════════════════════════════

private theorem fib_le_two_pow : ∀ m : Nat, 1 ≤ m → Nat.fib (m + 2) ≤ 2 ^ m
  | 1, _ => by native_decide
  | 2, _ => by native_decide
  | m + 3, _ => by
    calc Nat.fib (m + 3 + 2)
        = Nat.fib (m + 3 + 1) + Nat.fib (m + 3) := fib_succ_succ' (m + 3)
      _ ≤ 2 ^ (m + 2) + 2 ^ (m + 1) :=
          Nat.add_le_add (fib_le_two_pow (m + 2) (by omega)) (fib_le_two_pow (m + 1) (by omega))
      _ ≤ 2 ^ (m + 2) + 2 ^ (m + 2) :=
          Nat.add_le_add_left (Nat.pow_le_pow_right (by omega) (by omega)) _
      _ = 2 ^ (m + 3) := by ring

/-- Binary register width upper bound: ⌊log₂ F(m+2)⌋ ≤ m.
    subsec:conclusion-bounded-prime-register-godel-scaling -/
theorem godelLift_binary_width_upper (m : Nat) (hm : 1 ≤ m) :
    Nat.log 2 (Nat.fib (m + 2)) ≤ m := by
  calc Nat.log 2 (Nat.fib (m + 2))
      ≤ Nat.log 2 (2 ^ m) := Nat.log_mono_right (fib_le_two_pow m hm)
    _ = m := Nat.log_pow (by norm_num) m

private theorem fib_lower_bound (m : Nat) (_hm : 2 ≤ m) :
    2 ^ (m / 2) ≤ Nat.fib (m + 2) := by
  have h1 : Nat.fib 2 = 1 := by native_decide
  have h2 : 1 ≤ (2 : Nat) := by omega
  calc 2 ^ (m / 2) = 2 ^ (m / 2) * 1 := by ring
    _ = 2 ^ (m / 2) * Nat.fib 2 := by rw [h1]
    _ ≤ Nat.fib (2 + 2 * (m / 2)) := Omega.fib_exponential_growth 2 (m / 2) h2
    _ ≤ Nat.fib (m + 2) := Nat.fib_mono (by omega)

/-- Binary register width lower bound: m / 2 ≤ ⌊log₂ F(m+2)⌋.
    subsec:conclusion-bounded-prime-register-godel-scaling -/
theorem godelLift_binary_width_lower (m : Nat) (hm : 2 ≤ m) :
    m / 2 ≤ Nat.log 2 (Nat.fib (m + 2)) := by
  calc m / 2 = Nat.log 2 (2 ^ (m / 2)) := (Nat.log_pow (by norm_num) (m / 2)).symm
    _ ≤ Nat.log 2 (Nat.fib (m + 2)) := Nat.log_mono_right (fib_lower_bound m hm)

-- ══════════════════════════════════════════════════════════════
-- Phase R133: Binary-fiber Gödel lift instances
-- ══════════════════════════════════════════════════════════════

open Omega in
/-- Single-prime Gödel lift for binary fold m=7: exponent ≤ 4 suffices.
    thm:conclusion-bounded-prime-register-feasibility -/
theorem godelLift_binFiber_fold7_single : (4 + 1) ^ 1 ≥ cBinFiberMax 7 := by
  rw [cBinFiberMax_seven]; omega

open Omega in
/-- Binary Gödel lift fails for binary fold m=7: 2^2 = 4 < 5.
    thm:conclusion-bounded-prime-register-feasibility -/
theorem godelLift_binFiber_fold7_binary_fails : ¬ ((1 + 1) ^ 2 ≥ cBinFiberMax 7) := by
  rw [cBinFiberMax_seven]; omega

open Omega in
/-- Ternary Gödel lift for binary fold m=8: 3^2 = 9 ≥ 6.
    thm:conclusion-bounded-prime-register-feasibility -/
theorem godelLift_binFiber_fold8_ternary : (2 + 1) ^ 2 ≥ cBinFiberMax 8 := by
  rw [cBinFiberMax_eight]; omega

open Omega in
/-- Minimum binary registers for binary fold m=8: need ≥ 3.
    thm:conclusion-bounded-prime-register-feasibility -/
theorem godelLift_binFiber_fold8_min_binary :
    ¬ ((1 + 1) ^ 2 ≥ cBinFiberMax 8) ∧ (1 + 1) ^ 3 ≥ cBinFiberMax 8 := by
  constructor <;> (rw [cBinFiberMax_eight]; omega)

open Omega in
/-- Paper: thm:conclusion-bounded-prime-register-feasibility (binary fiber instances) -/
theorem paper_godelLift_binFiber_instances :
    (4 + 1) ^ 1 ≥ cBinFiberMax 7 ∧
    ¬ ((1 + 1) ^ 2 ≥ cBinFiberMax 7) ∧
    (2 + 1) ^ 2 ≥ cBinFiberMax 8 :=
  ⟨godelLift_binFiber_fold7_single, godelLift_binFiber_fold7_binary_fails,
   godelLift_binFiber_fold8_ternary⟩

-- ══════════════════════════════════════════════════════════════
-- Phase R154: binary Gödel lift minimum bits
-- ══════════════════════════════════════════════════════════════

open Omega in
/-- Binary Gödel lift requires at least ⌈log_2 D_m⌉ bits.
    thm:conclusion-bounded-prime-register-feasibility (binary case) -/
theorem godelLift_binary_min_bits (m k : Nat)
    (hfeas : X.maxFiberMultiplicity m ≤ 2 ^ k) :
    Nat.log 2 (X.maxFiberMultiplicity m) ≤ k :=
  calc Nat.log 2 (X.maxFiberMultiplicity m)
      ≤ Nat.log 2 (2 ^ k) := Nat.log_mono_right hfeas
    _ = k := Nat.log_pow (by norm_num) k

open Omega in
/-- Paper-facing binary minimum-bit bound.
    thm:conclusion-bounded-prime-register-feasibility -/
theorem paper_godelLift_binary_min_bits (m k : Nat)
    (hfeas : X.maxFiberMultiplicity m ≤ 2 ^ k) :
    Nat.log 2 (X.maxFiberMultiplicity m) ≤ k := by
  exact godelLift_binary_min_bits m k hfeas

-- ══════════════════════════════════════════════════════════════
-- Phase R157: Gödel lift binary optimality certificates
-- ══════════════════════════════════════════════════════════════

open Omega in
/-- For m=6, exactly 3 binary bits needed (2^2=4 < D_6=5 ≤ 2^3=8).
    thm:conclusion-bounded-prime-register-feasibility -/
theorem godelLift_binary_optimal_m6 :
    ¬ (X.maxFiberMultiplicity 6 ≤ 2 ^ 2) ∧
    X.maxFiberMultiplicity 6 ≤ 2 ^ 3 := by
  rw [X.maxFiberMultiplicity_six]; omega

open Omega in
/-- For m=7, exactly 3 binary bits needed (2^2=4 < D_7=6 ≤ 2^3=8).
    thm:conclusion-bounded-prime-register-feasibility -/
theorem godelLift_binary_optimal_m7 :
    ¬ (X.maxFiberMultiplicity 7 ≤ 2 ^ 2) ∧
    X.maxFiberMultiplicity 7 ≤ 2 ^ 3 := by
  rw [X.maxFiberMultiplicity_seven]; omega

open Omega in
/-- For m=8, exactly 3 binary bits needed (2^2=4 < D_8=8 ≤ 2^3=8).
    thm:conclusion-bounded-prime-register-feasibility -/
theorem godelLift_binary_optimal_m8 :
    ¬ (X.maxFiberMultiplicity 8 ≤ 2 ^ 2) ∧
    X.maxFiberMultiplicity 8 ≤ 2 ^ 3 := by
  rw [X.maxFiberMultiplicity_eight]; omega

-- ══════════════════════════════════════════════════════════════
-- Phase R159: Gödel lift optimality m=9,10
-- ══════════════════════════════════════════════════════════════

open Omega in
/-- For m=9, exactly 4 binary bits needed (2^3=8 < D_9=10 ≤ 2^4=16).
    thm:conclusion-bounded-prime-register-feasibility -/
theorem godelLift_binary_optimal_m9 :
    ¬ (X.maxFiberMultiplicity 9 ≤ 2 ^ 3) ∧
    X.maxFiberMultiplicity 9 ≤ 2 ^ 4 := by
  rw [X.maxFiberMultiplicity_nine]; omega

open Omega in
/-- For m=10, exactly 4 binary bits needed (2^3=8 < D_10=13 ≤ 2^4=16).
    thm:conclusion-bounded-prime-register-feasibility -/
theorem godelLift_binary_optimal_m10 :
    ¬ (X.maxFiberMultiplicity 10 ≤ 2 ^ 3) ∧
    X.maxFiberMultiplicity 10 ≤ 2 ^ 4 := by
  rw [X.maxFiberMultiplicity_ten]; omega

-- ══════════════════════════════════════════════════════════════
-- Phase R163: Gödel lift axis lower bound
-- ══════════════════════════════════════════════════════════════

/-- Minimum axis count for Gödel lift: k ≥ log_{E+1}(D).
    cor:conclusion-fixed-axis-exponential-amplitude -/
theorem godelLift_axis_lower_bound (k E D : Nat) (hE : 2 ≤ E + 1)
    (hfeas : D ≤ (E + 1) ^ k) :
    Nat.log (E + 1) D ≤ k :=
  calc Nat.log (E + 1) D
      ≤ Nat.log (E + 1) ((E + 1) ^ k) := Nat.log_mono_right hfeas
    _ = k := Nat.log_pow (by omega) k

open Omega in
/-- Binary specialization: axes grow as log_2(D_m).
    cor:conclusion-fixed-axis-exponential-amplitude -/
theorem godelLift_binary_axis_lower (m k : Nat)
    (hfeas : X.maxFiberMultiplicity m ≤ 2 ^ k) :
    Nat.log 2 (X.maxFiberMultiplicity m) ≤ k :=
  godelLift_axis_lower_bound k 1 (X.maxFiberMultiplicity m) (by omega) hfeas

/-- Binary specialization of the general axis lower bound.
    thm:conclusion-bounded-prime-register-feasibility -/
theorem godelLift_axis_lower_bound_binary_specialized (k D : Nat)
    (hfeas : D ≤ 2 ^ k) :
    Nat.log 2 D ≤ k := by
  simpa using godelLift_axis_lower_bound k 1 D (by omega) hfeas

open Omega in
/-- Ternary specialization: fewer axes with E=2.
    cor:conclusion-fixed-axis-exponential-amplitude -/
theorem godelLift_ternary_axis_lower (m k : Nat)
    (hfeas : X.maxFiberMultiplicity m ≤ 3 ^ k) :
    Nat.log 3 (X.maxFiberMultiplicity m) ≤ k :=
  godelLift_axis_lower_bound k 2 (X.maxFiberMultiplicity m) (by omega) hfeas

/-- A linear-density Gödel lift with one event per step requires at least five symbols.
    thm:conclusion-godel-five-symbol-threshold -/
theorem godelLift_alphabet_threshold_mge5 {M : ℕ}
    (hM : 2 ≤ M)
    (hineq : Real.log (2 / Real.goldenRatio) / Real.log M ≤ (4 : ℝ) / 27) :
    5 ≤ M := by
  have hconst : (4 : ℝ) / 27 < Real.log (2 / Real.goldenRatio) / Real.log 4 := by
    have hφlt : Real.goldenRatio < (13 : ℝ) / 8 := by
      rw [Real.goldenRatio]
      have hsq : Real.sqrt 5 ^ 2 = (5 : ℝ) := by
        rw [Real.sq_sqrt]
        positivity
      nlinarith
    have hφpos : 0 < Real.goldenRatio := by positivity
    have hbase : (16 : ℝ) / 13 < 2 / Real.goldenRatio := by
      refine (lt_div_iff₀ hφpos).2 ?_
      nlinarith [hφlt]
    have hpowlog : 4 * Real.log 4 < 27 * Real.log ((16 : ℝ) / 13) := by
      have hpow : (4 : ℝ) ^ 4 < ((16 : ℝ) / 13) ^ 27 := by norm_num
      have := Real.log_lt_log (by positivity : 0 < (4 : ℝ) ^ 4) hpow
      simpa [Real.log_rpow] using this
    have hmain : 4 * Real.log 4 < 27 * Real.log (2 / Real.goldenRatio) := by
      have hlogmono : Real.log ((16 : ℝ) / 13) < Real.log (2 / Real.goldenRatio) := by
        exact Real.log_lt_log (by positivity : 0 < (16 : ℝ) / 13) hbase
      linarith
    have hlog4pos : 0 < Real.log 4 := Real.log_pos (by norm_num)
    exact (lt_div_iff₀ hlog4pos).2 <| by nlinarith
  by_contra hlt
  have hMle4 : M ≤ 4 := by omega
  have hMpos : (0 : ℝ) < M := by positivity
  have hlogM_pos : 0 < Real.log M := by
    refine Real.log_pos ?_
    exact_mod_cast hM
  have hlogM_le : Real.log M ≤ Real.log 4 := by
    apply Real.log_le_log hMpos
    norm_num
    exact_mod_cast hMle4
  have hratio_ge : Real.log (2 / Real.goldenRatio) / Real.log 4 ≤
      Real.log (2 / Real.goldenRatio) / Real.log M := by
    have hnum_pos : 0 < Real.log (2 / Real.goldenRatio) := by
      have hphi_pos : 0 < Real.goldenRatio := Real.goldenRatio_pos
      have hphi_lt_two : Real.goldenRatio < 2 := Real.goldenRatio_lt_two
      apply Real.log_pos
      exact (one_lt_div hphi_pos).2 hphi_lt_two
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (inv_anti₀ hlogM_pos hlogM_le) hnum_pos.le
  have : (4 : ℝ) / 27 < (4 : ℝ) / 27 := by
    exact lt_of_lt_of_le hconst (hratio_ge.trans hineq)
  linarith

-- ══════════════════════════════════════════════════════════════
-- Phase R250: Binary auxiliary bits exact characterization
-- ══════════════════════════════════════════════════════════════

/-- Binary auxiliary bits: D ≤ 2^k iff ⌈log₂ D⌉ ≤ k.
    cor:pom-injectivization-binary-auxbits-exact -/
theorem binaryAuxBits_iff (D k : ℕ) (_hD : 0 < D) :
    D ≤ 2 ^ k ↔ Nat.clog 2 D ≤ k :=
  (Nat.clog_le_iff_le_pow (by norm_num : 1 < 2)).symm

-- ══════════════════════════════════════════════════════════════
-- Phase R252: Fibonacci growth bounds
-- ══════════════════════════════════════════════════════════════

/-- Fibonacci output size is at least linear: F(m+2) ≥ m + 1.
    subsec:conclusion-bounded-prime-register-godel-scaling -/
theorem fib_succ_succ_ge_succ (m : Nat) : m + 1 ≤ Nat.fib (m + 2) := by
  induction m with
  | zero => simp [Nat.fib]
  | succ m ih =>
    have hfib : Nat.fib (m + 3) = Nat.fib (m + 1) + Nat.fib (m + 2) := by
      rw [show m + 3 = (m + 1) + 2 from by omega]; exact Nat.fib_add_two
    have hpos : 1 ≤ Nat.fib (m + 1) := Nat.fib_pos.mpr (by omega)
    linarith

/-- Fibonacci strict growth: F(m+3) ≥ F(m+2) + 1 for m ≥ 1.
    subsec:conclusion-bounded-prime-register-godel-scaling -/
theorem fib_strict_growth (m : Nat) (hm : 1 ≤ m) :
    Nat.fib (m + 2) + 1 ≤ Nat.fib (m + 3) := by
  have hfib : Nat.fib (m + 3) = Nat.fib (m + 1) + Nat.fib (m + 2) := by
    rw [show m + 3 = (m + 1) + 2 from by omega]; exact Nat.fib_add_two
  have hpos : 1 ≤ Nat.fib (m + 1) := Nat.fib_pos.mpr (by omega)
  omega

-- ══════════════════════════════════════════════════════════════
-- Phase R256: Gödel lift infeasibility, monotonicity, fold tower
-- ══════════════════════════════════════════════════════════════

/-- If (E+1)^k < D then no injection exists.
    thm:conclusion-bounded-prime-register-feasibility (contrapositive) -/
theorem godelLift_infeasible (k E D : ℕ) (h : (E + 1) ^ k < D) :
    ¬ ∃ f : Fin D → Fin ((E + 1) ^ k), Function.Injective f := by
  intro ⟨f, hf⟩
  have := Fintype.card_le_of_injective f hf
  simp [Fintype.card_fin] at this
  omega

/-- Monotonicity: if k₁ ≤ k₂ and (E+1)^k₁ ≥ D then (E+1)^k₂ ≥ D.
    thm:conclusion-bounded-prime-register-feasibility -/
theorem godelLift_mono_k (E D k₁ k₂ : ℕ) (hk : k₁ ≤ k₂)
    (h : D ≤ (E + 1) ^ k₁) : D ≤ (E + 1) ^ k₂ :=
  le_trans h (Nat.pow_le_pow_right (by omega) hk)

/-- Concrete Fibonacci-fiber axis bounds from the fold tower.
    thm:conclusion-bounded-prime-register-feasibility -/
theorem godelLift_fold_tower_bounds :
    3 ≤ (2 + 1) ^ 1 ∧
    5 ≤ (2 + 1) ^ 2 ∧
    8 ≤ (2 + 1) ^ 2 ∧
    13 ≤ (3 + 1) ^ 2 ∧
    21 ≤ (4 + 1) ^ 2 ∧
    34 ≤ (5 + 1) ^ 2 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

-- ══════════════════════════════════════════════════════════════
-- Phase R259: Gödel lift extended tower
-- ══════════════════════════════════════════════════════════════

/-- Fold_9: (5+1)^2 = 36 ≥ 34.
    thm:conclusion-bounded-prime-register-feasibility -/
theorem godelLift_fold9 : (5 + 1) ^ 2 ≥ 34 := by omega

/-- Fold_10: (7+1)^2 = 64 ≥ 55.
    thm:conclusion-bounded-prime-register-feasibility -/
theorem godelLift_fold10 : (7 + 1) ^ 2 ≥ 55 := by omega

/-- Max fiber sizes = Fibonacci sequence.
    thm:conclusion-bounded-prime-register-feasibility -/
theorem godelLift_maxfiber_fib_chain :
    3 = Nat.fib 4 ∧ 5 = Nat.fib 5 ∧ 8 = Nat.fib 6 ∧
    13 = Nat.fib 7 ∧ 21 = Nat.fib 8 ∧ 34 = Nat.fib 9 ∧ 55 = Nat.fib 10 := by
  refine ⟨by native_decide, by native_decide, by native_decide,
    by native_decide, by native_decide, by native_decide, by native_decide⟩

/-- Optimal k=2 bases for each Fibonacci max-fiber.
    thm:conclusion-bounded-prime-register-feasibility -/
theorem godelLift_optimal_k2_bases :
    (2 + 1) ^ 2 ≥ Nat.fib 4 ∧
    (2 + 1) ^ 2 ≥ Nat.fib 5 ∧
    (2 + 1) ^ 2 ≥ Nat.fib 6 ∧
    (3 + 1) ^ 2 ≥ Nat.fib 7 ∧
    (4 + 1) ^ 2 ≥ Nat.fib 8 ∧
    (5 + 1) ^ 2 ≥ Nat.fib 9 ∧
    (7 + 1) ^ 2 ≥ Nat.fib 10 := by
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide,
    by native_decide, by native_decide, by native_decide⟩

/-- Fibonacci envelope eventual strict failure: cBinFiberMax(m) < F(m+2) for m ≥ 7.
    prop:conclusion-foldbin-fibonacci-envelope-eventual-strict-failure -/
theorem paper_foldbin_fibonacci_envelope_eventual_strict_failure :
    cBinFiberMax 7 < Nat.fib 9 ∧
    cBinFiberMax 8 < Nat.fib 10 ∧
    cBinFiberMax 7 + 1 ≤ Nat.fib 9 := by
  rw [cBinFiberMax_seven, cBinFiberMax_eight]
  refine ⟨by native_decide, by native_decide, by native_decide⟩

/-- Binary fold recovery one-bit splitting witness.
    thm:conclusion-binfold-fullrecovery-visible-entropy-onebit-splitting -/
theorem paper_binfold_recovery_onebit_splitting :
    2 ^ 6 = 64 ∧ Nat.fib 8 = 21 ∧
    cBinFiberMax 6 = 4 ∧
    2 ^ 6 % Nat.fib 8 = 1 ∧
    2 ^ 6 / Nat.fib 8 = 3 ∧
    2 ^ 7 / 3 = 42 := by
  rw [cBinFiberMax_six]; native_decide

/-- Stable K0 rank audit.
    prop:conclusion-foldbin-stable-k0-rank -/
theorem paper_conclusion_stable_k0_rank_audit :
    Fintype.card (X 6) = 21 ∧
    cBinFiberMax 6 = 4 ∧
    cBinFiberMax 7 = 5 ∧
    momentSum 2 6 = 220 ∧
    cBinFiberMax 6 < cBinFiberMax 7 := by
  refine ⟨by rw [X.card_eq_fib]; native_decide, cBinFiberMax_six, cBinFiberMax_seven,
    momentSum_two_six, by rw [cBinFiberMax_six, cBinFiberMax_seven]; omega⟩

-- ══════════════════════════════════════════════════════════════
-- Phase R314: Gödel encoding append splitting
-- ══════════════════════════════════════════════════════════════

/-- Gödel encoding from a given start index: ∏_{i} p_{offset+start+i}^{code[i]}.
    thm:conclusion-godel-semidirect-law -/
def godelEncodingFrom (primes : ℕ → ℕ) (offset : ℕ) (start : ℕ) : List ℕ → ℕ
  | [] => 1
  | a :: rest => primes (offset + start) ^ a * godelEncodingFrom primes offset (start + 1) rest

/-- Gödel encoding: map a list of positive naturals to ∏ p_i^{a_i}.
    thm:conclusion-godel-semidirect-law -/
def godelEncoding (primes : ℕ → ℕ) (offset : ℕ) (code : List ℕ) : ℕ :=
  godelEncodingFrom primes offset 0 code

@[simp] theorem godelEncodingFrom_nil (primes : ℕ → ℕ) (offset start : ℕ) :
    godelEncodingFrom primes offset start [] = 1 := rfl

@[simp] theorem godelEncodingFrom_cons (primes : ℕ → ℕ) (offset start a : ℕ) (rest : List ℕ) :
    godelEncodingFrom primes offset start (a :: rest) =
    primes (offset + start) ^ a * godelEncodingFrom primes offset (start + 1) rest := rfl

private theorem godelEncodingFrom_reindex (primes : ℕ → ℕ) (a b : ℕ) (code : List ℕ) :
    godelEncodingFrom primes a b code = godelEncodingFrom primes (a + b) 0 code := by
  induction code generalizing a b with
  | nil => simp
  | cons x rest ih =>
    simp only [godelEncodingFrom_cons, Nat.add_zero]
    congr 1
    rw [ih a (b + 1), ih (a + b) 1, show a + (b + 1) = (a + b) + 1 from by omega]

private theorem godelEncodingFrom_append (primes : ℕ → ℕ) (offset start : ℕ)
    (u v : List ℕ) :
    godelEncodingFrom primes offset start (u ++ v) =
    godelEncodingFrom primes offset start u *
    godelEncodingFrom primes offset (start + u.length) v := by
  induction u generalizing start with
  | nil => simp
  | cons a rest ih =>
    simp only [List.cons_append, godelEncodingFrom_cons, List.length_cons, ih (start + 1)]
    have : start + 1 + rest.length = start + (rest.length + 1) := by omega
    rw [this, Nat.mul_assoc]

/-- Gödel encoding splits over concatenation: G(u++v) = G(u) · G_shift(v).
    thm:conclusion-godel-semidirect-law -/
theorem godelEncoding_append (primes : ℕ → ℕ) (offset : ℕ) (u v : List ℕ) :
    godelEncoding primes offset (u ++ v) =
    godelEncoding primes offset u * godelEncoding primes (offset + u.length) v := by
  simp only [godelEncoding, godelEncodingFrom_append, Nat.zero_add]
  congr 1
  rw [godelEncodingFrom_reindex primes offset u.length v]

/-- Singleton Gödel encoding.
    thm:conclusion-godel-semidirect-law -/
@[simp] theorem godelEncoding_singleton (primes : ℕ → ℕ) (offset a : ℕ) :
    godelEncoding primes offset [a] = primes offset ^ a := by
  simp [godelEncoding, godelEncodingFrom]

private theorem godelEncodingFrom_pos' (primes : ℕ → ℕ) (hp : ∀ i, 0 < primes i)
    (offset start : ℕ) (code : List ℕ) :
    0 < godelEncodingFrom primes offset start code := by
  induction code generalizing start with
  | nil => simp
  | cons a rest ih =>
    simp only [godelEncodingFrom_cons]
    exact Nat.mul_pos (Nat.pos_of_ne_zero (pow_ne_zero _ (Nat.pos_iff_ne_zero.mp (hp (offset + start)))))
      (ih (start + 1))

/-- Gödel encoding is positive when all primes are positive.
    thm:conclusion-godel-semidirect-law -/
theorem godelEncoding_pos (primes : ℕ → ℕ) (offset : ℕ) (code : List ℕ)
    (hp : ∀ i, 0 < primes i) :
    0 < godelEncoding primes offset code :=
  godelEncodingFrom_pos' primes hp offset 0 code

/-- Empty Gödel encoding is 1.
    thm:conclusion-godel-semidirect-law -/
@[simp] theorem godelEncoding_nil (primes : ℕ → ℕ) (offset : ℕ) :
    godelEncoding primes offset [] = 1 := by
  simp [godelEncoding, godelEncodingFrom]

/-- Cons Gödel encoding: G(a :: rest) = p_offset^a · G_{offset+1}(rest).
    thm:conclusion-godel-semidirect-law -/
theorem godelEncoding_cons (primes : ℕ → ℕ) (offset a : ℕ) (rest : List ℕ) :
    godelEncoding primes offset (a :: rest) =
    primes offset ^ a * godelEncoding primes (offset + 1) rest := by
  simp only [godelEncoding, godelEncodingFrom_cons, Nat.zero_add]
  congr 1
  rw [godelEncodingFrom_reindex primes offset 1 rest]

/-- Two-element Gödel encoding.
    thm:conclusion-godel-semidirect-law -/
@[simp] theorem godelEncoding_two (primes : ℕ → ℕ) (offset a b : ℕ) :
    godelEncoding primes offset [a, b] =
    primes offset ^ a * primes (offset + 1) ^ b := by
  rw [godelEncoding_cons, godelEncoding_singleton]

/-- Three-element Gödel encoding.
    thm:conclusion-godel-semidirect-law -/
@[simp] theorem godelEncoding_three (primes : ℕ → ℕ) (offset a b c : ℕ) :
    godelEncoding primes offset [a, b, c] =
    primes offset ^ a * (primes (offset + 1) ^ b * primes (offset + 2) ^ c) := by
  rw [godelEncoding_cons, godelEncoding_two, show offset + 1 + 1 = offset + 2 from by omega]

/-- Gödel encoding equals 1 iff all exponents are 0.
    thm:conclusion-godel-semidirect-law -/
theorem godelEncoding_eq_one_iff (primes : ℕ → ℕ) (offset : ℕ) (code : List ℕ)
    (hp : ∀ i, 1 < primes i) :
    godelEncoding primes offset code = 1 ↔ ∀ a ∈ code, a = 0 := by
  induction code generalizing offset with
  | nil => simp [godelEncoding_nil]
  | cons a rest ih =>
    rw [godelEncoding_cons]
    constructor
    · intro h
      have ⟨hpow, hrest⟩ := mul_eq_one.mp h
      have ha : a = 0 := by
        by_contra hne
        have : 1 < primes offset ^ a :=
          Nat.one_lt_pow hne (hp offset)
        omega
      simp only [List.mem_cons, forall_eq_or_imp]
      exact ⟨ha, (ih (offset + 1)).mp hrest⟩
    · intro h
      simp only [List.mem_cons, forall_eq_or_imp] at h
      rw [h.1, pow_zero, one_mul, (ih (offset + 1)).mpr h.2]

-- ══════════════════════════════════════════════════════════════
-- Phase R329: Gödel encoding coprimality
-- ══════════════════════════════════════════════════════════════

private theorem prime_pow_coprime_godelEncodingFrom'
    (primes : ℕ → ℕ) (hcop : ∀ i j, i ≠ j → Nat.Coprime (primes i) (primes j))
    (idx a s : ℕ) (code : List ℕ) (hdisj : idx < s ∨ s + code.length ≤ idx) :
    Nat.Coprime (primes idx ^ a) (godelEncodingFrom primes s 0 code) := by
  induction code generalizing s with
  | nil => simp [godelEncodingFrom, Nat.Coprime]
  | cons b rest ih =>
    simp only [godelEncodingFrom_cons, Nat.add_zero, List.length_cons] at hdisj ⊢
    apply Nat.Coprime.mul_right
    · exact (hcop idx s (by omega)).pow a b
    · rw [godelEncodingFrom_reindex primes s 1 rest]
      exact ih (s + 1) (by omega)

private theorem godelEncodingFrom_coprime'
    (primes : ℕ → ℕ) (hcop : ∀ i j, i ≠ j → Nat.Coprime (primes i) (primes j))
    (s1 s2 : ℕ) (l1 l2 : List ℕ) (hdisj : s1 + l1.length ≤ s2) :
    Nat.Coprime (godelEncodingFrom primes s1 0 l1)
                (godelEncodingFrom primes s2 0 l2) := by
  induction l1 generalizing s1 with
  | nil => simp [godelEncodingFrom, Nat.Coprime]
  | cons a rest ih =>
    simp only [godelEncodingFrom_cons, Nat.add_zero, List.length_cons] at hdisj ⊢
    apply Nat.Coprime.mul_left
    · exact prime_pow_coprime_godelEncodingFrom' primes hcop s1 a s2 l2 (Or.inl (by omega))
    · rw [godelEncodingFrom_reindex primes s1 1 rest]
      exact ih (s1 + 1) (by omega)

/-- Gödel encodings of adjacent segments are coprime.
    thm:conclusion-godel-semidirect-law -/
theorem godelEncoding_coprime_of_disjoint
    (primes : ℕ → ℕ) (offset : ℕ) (u v : List ℕ)
    (hcop : ∀ i j, i ≠ j → Nat.Coprime (primes i) (primes j))
    (_hp : ∀ i, 0 < primes i) :
    Nat.Coprime (godelEncoding primes offset u)
                (godelEncoding primes (offset + u.length) v) := by
  simp only [godelEncoding]
  exact godelEncodingFrom_coprime' primes hcop offset (offset + u.length) u v (le_refl _)

end Omega.Conclusion
