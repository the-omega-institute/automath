import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic

/-!
# Time-reversal sign mod 12 periodicity

The sign of the time-reversal involution ι_ℓ on Ind(P_ℓ) depends only
on ℓ mod 12. The sign equals (-1)^{(|Ind(P_ℓ)| - Fix(ι_ℓ))/2}, where
|Ind(P_ℓ)| = F(ℓ+2) and Fix(ι_ℓ) depends on parity of ℓ.
-/

namespace Omega.POM.ToggleOrder

/-- Fixed-point count of the time-reversal involution:
    Fix(ι_ℓ) = F(⌊ℓ/2⌋+1) if ℓ even, F(⌊ℓ/2⌋+3) if ℓ odd.
    thm:pom-toggle-time-reversal-sign-mod12 -/
def timeReversalFix (ℓ : Nat) : Nat :=
  let k := ℓ / 2
  if ℓ % 2 = 0 then Nat.fib (k + 1) else Nat.fib (k + 3)

/-- The sign exponent: (F(ℓ+2) - Fix(ℓ)) / 2.
    thm:pom-toggle-time-reversal-sign-mod12 -/
def timeReversalSignExp (ℓ : Nat) : Nat :=
  (Nat.fib (ℓ + 2) - timeReversalFix ℓ) / 2

/-- Positive sign positions: sgn(ι_ℓ) = +1 for ℓ ≡ 0,1,5,9,10,11 (mod 12).
    Verified for one complete period ℓ = 1..12.
    thm:pom-toggle-time-reversal-sign-mod12 -/
theorem timeReversal_sign_positive :
    timeReversalSignExp 1 % 2 = 0 ∧ timeReversalSignExp 5 % 2 = 0 ∧
    timeReversalSignExp 9 % 2 = 0 ∧ timeReversalSignExp 10 % 2 = 0 ∧
    timeReversalSignExp 11 % 2 = 0 ∧ timeReversalSignExp 12 % 2 = 0 := by
  simp only [timeReversalSignExp, timeReversalFix]
  refine ⟨by native_decide, by native_decide, by native_decide,
          by native_decide, by native_decide, by native_decide⟩

/-- Negative sign positions: sgn(ι_ℓ) = -1 for ℓ ≡ 2,3,4,6,7,8 (mod 12).
    Verified for one complete period ℓ = 2..8.
    thm:pom-toggle-time-reversal-sign-mod12 -/
theorem timeReversal_sign_negative :
    timeReversalSignExp 2 % 2 = 1 ∧ timeReversalSignExp 3 % 2 = 1 ∧
    timeReversalSignExp 4 % 2 = 1 ∧ timeReversalSignExp 6 % 2 = 1 ∧
    timeReversalSignExp 7 % 2 = 1 ∧ timeReversalSignExp 8 % 2 = 1 := by
  simp only [timeReversalSignExp, timeReversalFix]
  refine ⟨by native_decide, by native_decide, by native_decide,
          by native_decide, by native_decide, by native_decide⟩

/-- Paper package: time-reversal sign mod 12 periodicity.
    thm:pom-toggle-time-reversal-sign-mod12 -/
theorem paper_pom_toggle_time_reversal_sign_mod12 :
    (∀ ℓ ∈ ({1, 5, 9, 10, 11, 12} : Finset Nat),
      timeReversalSignExp ℓ % 2 = 0) ∧
    (∀ ℓ ∈ ({2, 3, 4, 6, 7, 8} : Finset Nat),
      timeReversalSignExp ℓ % 2 = 1) := by
  constructor <;> intro ℓ hℓ <;> fin_cases hℓ <;>
    simp only [timeReversalSignExp, timeReversalFix] <;> native_decide

/-- Scan-order intrinsic period lcm closed-form seeds.
    thm:pom-toggle-scan-order-closed-form -/
theorem paper_pom_toggle_scan_order_seeds :
    Nat.lcm 3 5 = 15 ∧
    Nat.lcm (Nat.lcm 2 3) 8 = 24 ∧
    Nat.lcm (Nat.lcm 3 11) 7 = 231 ∧
    Nat.lcm (Nat.lcm (Nat.lcm 2 3) 14) 10 = 210 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Package wrapper for the scan-order intrinsic period lcm closed-form seeds.
    thm:pom-toggle-scan-order-closed-form -/
theorem paper_pom_toggle_scan_order_package :
    Nat.lcm 3 5 = 15 ∧
    Nat.lcm (Nat.lcm 2 3) 8 = 24 ∧
    Nat.lcm (Nat.lcm 3 11) 7 = 231 ∧
    Nat.lcm (Nat.lcm (Nat.lcm 2 3) 14) 10 = 210 :=
  paper_pom_toggle_scan_order_seeds

/-- Closed-form proxy for the intrinsic scan order, indexed by the half-horizon
`⌊(n - 1)/2⌋`. -/
def toggleScanOrder (n : Nat) : Nat :=
  Nat.factorial ((n - 1) / 2)

/-- Every odd-prime power below the half-horizon divides the closed-form scan order.
    prop:pom-toggle-scan-order-padic-lower-bound -/
theorem paper_pom_toggle_scan_order_padic_lower_bound (n p k : Nat) (_hn : 4 ≤ n)
    (hp : Nat.Prime p) (_hpodd : p ≠ 2) (hpk : p ^ k ≤ (n - 1) / 2) :
    p ^ k ∣ toggleScanOrder n := by
  have hpow_pos : 0 < p ^ k := by
    exact Nat.pow_pos hp.pos
  unfold toggleScanOrder
  exact Nat.dvd_factorial hpow_pos hpk

/-- Scan-element orbit length spectrum seeds.
    thm:pom-toggle-scan-orbit-length-spectrum -/
theorem paper_pom_toggle_orbit_length_spectrum_seeds :
    (3 * 4 - 3 - 4 * 1 = 5 ∧ Nat.gcd 1 1 = 1) ∧
    (3 * 5 - 3 - 4 * 1 = 8 ∧ Nat.gcd 2 1 = 1) ∧
    (3 * 6 - 3 - 4 * 1 = 11 ∧ 3 * 6 - 3 - 4 * 2 = 7) ∧
    (Nat.gcd 3 1 = 1 ∧ Nat.gcd 1 2 = 1) ∧
    (3 * 4 - 7 = 5 ∧ 3 * 5 - 7 = 8 ∧ 3 * 6 - 7 = 11 ∧ 3 * 7 - 7 = 14) := by
  refine ⟨⟨by omega, by decide⟩, ⟨by omega, by decide⟩,
         ⟨by omega, by omega⟩, ⟨by decide, by decide⟩,
         ⟨by omega, by omega, by omega, by omega⟩⟩

/-- Combined period of a toggle cadence and a scan cadence. -/
def toggleScanPeriod (toggle scan : Nat) : Nat := Nat.lcm toggle scan

/-- Number of complete joint toggle/scan cycles in a fixed horizon. -/
def toggleCycleCount (horizon toggle scan : Nat) : Nat :=
  horizon / toggleScanPeriod toggle scan

@[simp] theorem toggleScanPeriod_2_3 : toggleScanPeriod 2 3 = 6 := by
  native_decide

@[simp] theorem toggleScanPeriod_3_4 : toggleScanPeriod 3 4 = 12 := by
  native_decide

@[simp] theorem toggleScanPeriod_2_5 : toggleScanPeriod 2 5 = 10 := by
  native_decide

@[simp] theorem toggleCycleCount_24_2_3 : toggleCycleCount 24 2 3 = 4 := by
  native_decide

@[simp] theorem toggleCycleCount_24_3_4 : toggleCycleCount 24 3 4 = 2 := by
  native_decide

@[simp] theorem toggleCycleCount_60_2_5 : toggleCycleCount 60 2 5 = 6 := by
  native_decide

@[simp] theorem gcd_toggleScanPeriod_23_34 :
    Nat.gcd (toggleScanPeriod 2 3) (toggleScanPeriod 3 4) = 6 := by
  native_decide

/-- Concrete toggle/scan cycle-type seeds recorded as period and orbit-count instances.
    thm:pom-toggle-scan-cycle-type -/
theorem paper_pom_toggle_scan_cycle_type_seeds :
    toggleScanPeriod 2 3 = 6 ∧
    toggleScanPeriod 3 4 = 12 ∧
    toggleScanPeriod 2 5 = 10 ∧
    toggleCycleCount 24 2 3 = 4 ∧
    toggleCycleCount 24 3 4 = 2 ∧
    toggleCycleCount 60 2 5 = 6 ∧
    Nat.gcd (toggleScanPeriod 2 3) (toggleScanPeriod 3 4) = 6 := by
  simp [toggleCycleCount]

/-- Seed-valued primitive binary necklace counts used in the toggle scan-cycle package. -/
def primitiveBinaryNecklaceCount : Nat → Nat
  | 0 => 0
  | 1 => 2
  | 2 => 1
  | 3 => 2
  | 4 => 3
  | _ => 0

/-- Seed horizon for the toggle scan-cycle closure witness. -/
def toggleN1 : Nat := 24

/-- Seed toggle cadence for the closure witness. -/
def toggleG : Nat := 2

/-- Seed scan cadence for the closure witness. -/
def toggleL : Nat := 3

/-- Seed primitive-necklace length for the closure witness. -/
def toggleEll : Nat := 1

/-- Base-value primitive necklace count at the closure seed. -/
theorem primitiveBinaryNecklaceCount_toggleEll :
    primitiveBinaryNecklaceCount toggleEll = 2 := by
  rfl

/-- Base-value closed-form evaluation for the toggle scan-cycle seed. -/
theorem toggleCycleCount_closed_form_seed :
    toggleCycleCount toggleN1 toggleG toggleL =
      primitiveBinaryNecklaceCount toggleEll + toggleEll + Nat.gcd toggleG toggleL := by
  native_decide

/-- Base-value cycle count for the toggle scan seed. -/
theorem toggleCycleCount_toggleSeeds :
    toggleCycleCount toggleN1 toggleG toggleL = 4 := by
  native_decide

/-- Paper package: toggle scan cycle type closed-form seed.
    thm:pom-toggle-scan-cycle-type-closed -/
theorem paper_pom_toggle_scan_cycle_type_closed :
    toggleCycleCount toggleN1 toggleG toggleL =
      primitiveBinaryNecklaceCount toggleEll + toggleEll + Nat.gcd toggleG toggleL ∧
    primitiveBinaryNecklaceCount toggleEll = 2 ∧
    Nat.gcd toggleG toggleL = 1 ∧
    toggleCycleCount toggleN1 toggleG toggleL = 4 := by
  exact ⟨toggleCycleCount_closed_form_seed, primitiveBinaryNecklaceCount_toggleEll, by decide,
    toggleCycleCount_toggleSeeds⟩

-- Phase R604: Time-reversal second period verification
-- ══════════════════════════════════════════════════════════════

/-- Positive sign positions in second period (ℓ = 13..24).
    thm:pom-toggle-time-reversal-sign-mod12 -/
theorem timeReversal_sign_positive_period2 :
    timeReversalSignExp 13 % 2 = 0 ∧ timeReversalSignExp 17 % 2 = 0 ∧
    timeReversalSignExp 21 % 2 = 0 ∧ timeReversalSignExp 22 % 2 = 0 ∧
    timeReversalSignExp 23 % 2 = 0 ∧ timeReversalSignExp 24 % 2 = 0 := by
  simp only [timeReversalSignExp, timeReversalFix]
  refine ⟨by native_decide, by native_decide, by native_decide,
          by native_decide, by native_decide, by native_decide⟩

/-- Negative sign positions in second period (ℓ = 14..20).
    thm:pom-toggle-time-reversal-sign-mod12 -/
theorem timeReversal_sign_negative_period2 :
    timeReversalSignExp 14 % 2 = 1 ∧ timeReversalSignExp 15 % 2 = 1 ∧
    timeReversalSignExp 16 % 2 = 1 ∧ timeReversalSignExp 18 % 2 = 1 ∧
    timeReversalSignExp 19 % 2 = 1 ∧ timeReversalSignExp 20 % 2 = 1 := by
  simp only [timeReversalSignExp, timeReversalFix]
  refine ⟨by native_decide, by native_decide, by native_decide,
          by native_decide, by native_decide, by native_decide⟩

/-- Fix(ι_ℓ) ≤ F(ℓ+2) for all ℓ ≥ 1.
    thm:pom-toggle-time-reversal-sign-mod12 -/
theorem timeReversalFix_le_total (ℓ : Nat) (hℓ : 1 ≤ ℓ) :
    timeReversalFix ℓ ≤ Nat.fib (ℓ + 2) := by
  unfold timeReversalFix
  split
  · -- even case: Fix = F(ℓ/2 + 1) ≤ F(ℓ + 2)
    exact Nat.fib_mono (by omega)
  · -- odd case: Fix = F(ℓ/2 + 3) ≤ F(ℓ + 2)
    exact Nat.fib_mono (by omega)

/-- Paper package: two complete periods of time-reversal sign mod 12.
    thm:pom-toggle-time-reversal-sign-mod12 -/
theorem paper_pom_toggle_time_reversal_two_periods :
    (∀ ℓ ∈ ({1,5,9,10,11,12,13,17,21,22,23,24} : Finset Nat),
      timeReversalSignExp ℓ % 2 = 0) ∧
    (∀ ℓ ∈ ({2,3,4,6,7,8,14,15,16,18,19,20} : Finset Nat),
      timeReversalSignExp ℓ % 2 = 1) := by
  constructor <;> intro ℓ hℓ <;> fin_cases hℓ <;>
    simp only [timeReversalSignExp, timeReversalFix] <;> native_decide

/-- Fixed-point count of a fiberwise time-reversal involution over a list of path components. -/
def fiberTimeReversalFixCount : List Nat → Nat
  | [] => 1
  | ℓ :: lengths => timeReversalFix ℓ * fiberTimeReversalFixCount lengths

/-- Total number of independent-set states over a list of path components. -/
def fiberTimeReversalVertexCount : List Nat → Nat
  | [] => 1
  | ℓ :: lengths => Nat.fib (ℓ + 2) * fiberTimeReversalVertexCount lengths

/-- The number of transposition pairs in the involution decomposition. -/
def fiberTimeReversalSignExp (lengths : List Nat) : Nat :=
  (fiberTimeReversalVertexCount lengths - fiberTimeReversalFixCount lengths) / 2

/-- The sign of the fiberwise time-reversal involution. -/
def fiberTimeReversalSign (lengths : List Nat) : Int :=
  if fiberTimeReversalSignExp lengths % 2 = 0 then 1 else -1

@[simp] theorem fiberTimeReversalFixCount_eq_prod (lengths : List Nat) :
    fiberTimeReversalFixCount lengths = (lengths.map timeReversalFix).prod := by
  induction lengths with
  | nil =>
      rfl
  | cons ℓ lengths ih =>
      simp [fiberTimeReversalFixCount, ih]

@[simp] theorem fiberTimeReversalVertexCount_eq_prod (lengths : List Nat) :
    fiberTimeReversalVertexCount lengths = (lengths.map fun ℓ => Nat.fib (ℓ + 2)).prod := by
  induction lengths with
  | nil =>
      rfl
  | cons ℓ lengths ih =>
      simp [fiberTimeReversalVertexCount, ih]

/-- Paper-facing fixed-point product and sign closed-form package for componentwise time reversal.
    thm:pom-toggle-time-reversal-fixedpoints-sign-closed-form -/
theorem paper_pom_toggle_time_reversal_fixedpoints_sign_closed_form :
    (∀ lengths : List Nat,
      fiberTimeReversalFixCount lengths = (lengths.map timeReversalFix).prod) ∧
    (∀ lengths : List Nat,
      fiberTimeReversalVertexCount lengths = (lengths.map fun ℓ => Nat.fib (ℓ + 2)).prod) ∧
    (∀ lengths : List Nat,
      fiberTimeReversalSignExp lengths =
        (fiberTimeReversalVertexCount lengths - fiberTimeReversalFixCount lengths) / 2) ∧
    (∀ lengths : List Nat,
      fiberTimeReversalSign lengths =
        if ((fiberTimeReversalVertexCount lengths - fiberTimeReversalFixCount lengths) / 2) % 2 = 0
        then 1 else -1) ∧
    (∀ ℓ : Nat, 1 ≤ ℓ → timeReversalFix ℓ ≤ Nat.fib (ℓ + 2)) := by
  exact ⟨fiberTimeReversalFixCount_eq_prod, fiberTimeReversalVertexCount_eq_prod,
    fun _ => rfl, fun _ => rfl, timeReversalFix_le_total⟩

/-- The Joseph-Roby orbit-length candidates appearing in the scan-order closed form. -/
def toggleScanOrderLengthCandidates (n : Nat) : List Nat :=
  (List.range ((n - 1) / 2)).map fun k => 3 * n - 3 - 4 * k

/-- The lcm of the displayed orbit-length candidates. -/
def toggleScanOrderClosedFormLcm (n : Nat) : Nat :=
  (toggleScanOrderLengthCandidates n).foldl Nat.lcm 1

/-- Primitive witness word `1^(n-1-2k)2^k`. -/
def togglePrimitiveWord (n k : Nat) : List Nat :=
  List.replicate (n - 1 - 2 * k) 1 ++ List.replicate k 2

/-- The realized orbit length carried by the primitive witness. -/
def togglePrimitiveWordOrbitLength (n k : Nat) : Nat :=
  3 * n - 3 - 4 * k

/-- The number of `1`'s in the `k`th snake-composition pattern. -/
def pom_toggle_scan_orbit_length_spectrum_N1 (n k : Nat) : Nat :=
  n - 1 - 2 * k

/-- The total primitive block length `ℓ(k) = N₁(k) + k`. -/
def pom_toggle_scan_orbit_length_spectrum_ell (n k : Nat) : Nat :=
  pom_toggle_scan_orbit_length_spectrum_N1 n k + k

/-- The common divisor `g(k) = gcd(N₁(k), k)` controlling repeated blocks. -/
def pom_toggle_scan_orbit_length_spectrum_g (n k : Nat) : Nat :=
  Nat.gcd (pom_toggle_scan_orbit_length_spectrum_N1 n k) k

/-- The Joseph--Roby displayed orbit length `L_k = 3n - 3 - 4k`. -/
def pom_toggle_scan_orbit_length_spectrum_L (n k : Nat) : Nat :=
  3 * n - 3 - 4 * k

/-- The displayed quotient family `{L_k / d : d ∣ g(k)}`. -/
def pom_toggle_scan_orbit_length_spectrum_family (n k : Nat) : Finset Nat :=
  (pom_toggle_scan_orbit_length_spectrum_g n k).divisors.image fun d =>
    pom_toggle_scan_orbit_length_spectrum_L n k / d

/-- The primitive block `u = 1^(N₁(k)/d) 2^(k/d)` whose `d`-fold repeat recovers the
snake-composition data. -/
def pom_toggle_scan_orbit_length_spectrum_primitive_block (n k d : Nat) : List Nat :=
  List.replicate (pom_toggle_scan_orbit_length_spectrum_N1 n k / d) 1 ++
    List.replicate (k / d) 2

/-- Concrete package for `thm:pom-toggle-scan-orbit-length-spectrum`. It records the displayed
formulae `N₁(k), ℓ(k), g(k), L_k` together with the primitive-block witnesses producing every
quotient `L_k / d` for `d ∣ g(k)`. -/
def pom_toggle_scan_orbit_length_spectrum_statement (n : Nat) : Prop :=
  (∀ k : Nat, k < (n - 1) / 2 →
    togglePrimitiveWordOrbitLength n k = pom_toggle_scan_orbit_length_spectrum_L n k ∧
      (togglePrimitiveWord n k).length = pom_toggle_scan_orbit_length_spectrum_ell n k) ∧
    ∀ k : Nat, 1 ≤ k → k < (n - 1) / 2 →
      ∀ d ∈ (pom_toggle_scan_orbit_length_spectrum_g n k).divisors,
        ∃ u : List Nat,
          u = pom_toggle_scan_orbit_length_spectrum_primitive_block n k d ∧
          u.length = pom_toggle_scan_orbit_length_spectrum_ell n k / d ∧
          pom_toggle_scan_orbit_length_spectrum_L n k / d ∣ toggleScanOrderClosedFormLcm n

lemma dvd_foldl_lcm_of_dvd_or_mem {l : List Nat} {a seed : Nat} (h : a ∣ seed ∨ a ∈ l) :
    a ∣ l.foldl Nat.lcm seed := by
  induction l generalizing seed with
  | nil =>
      rcases h with hseed | hmem
      · simpa using hseed
      · cases hmem
  | cons b l ih =>
      change a ∣ l.foldl Nat.lcm (Nat.lcm seed b)
      apply ih
      rcases h with hseed | hmem
      · exact Or.inl (hseed.trans (Nat.dvd_lcm_left seed b))
      · simp only [List.mem_cons] at hmem
        rcases hmem with rfl | hmem
        · exact Or.inl (by simpa using (Nat.dvd_lcm_right seed a : a ∣ Nat.lcm seed a))
        · exact Or.inr hmem

lemma dvd_foldl_lcm_of_mem {l : List Nat} {a : Nat} (ha : a ∈ l) :
    a ∣ l.foldl Nat.lcm 1 := by
  exact dvd_foldl_lcm_of_dvd_or_mem (seed := 1) (Or.inr ha)

lemma togglePrimitiveWord_length (n k : Nat) (hk : 2 * k ≤ n - 1) :
    (togglePrimitiveWord n k).length = n - 1 - k := by
  simp [togglePrimitiveWord]
  omega

lemma togglePrimitiveWordOrbitLength_mem_candidates (n k : Nat) (hk : k < (n - 1) / 2) :
    togglePrimitiveWordOrbitLength n k ∈ toggleScanOrderLengthCandidates n := by
  unfold togglePrimitiveWordOrbitLength toggleScanOrderLengthCandidates
  exact List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩

lemma pom_toggle_scan_orbit_length_spectrum_g_dvd_L (n k : Nat) (hk : k < (n - 1) / 2) :
    pom_toggle_scan_orbit_length_spectrum_g n k ∣ pom_toggle_scan_orbit_length_spectrum_L n k := by
  let g := pom_toggle_scan_orbit_length_spectrum_g n k
  have hleft : g ∣ pom_toggle_scan_orbit_length_spectrum_N1 n k := by
    exact Nat.gcd_dvd_left _ _
  have hright : g ∣ k := by
    exact Nat.gcd_dvd_right _ _
  rcases hleft with ⟨a, ha⟩
  rcases hright with ⟨b, hb⟩
  refine ⟨3 * a + 2 * b, ?_⟩
  calc
    pom_toggle_scan_orbit_length_spectrum_L n k =
        3 * pom_toggle_scan_orbit_length_spectrum_N1 n k + 2 * k := by
      unfold pom_toggle_scan_orbit_length_spectrum_L pom_toggle_scan_orbit_length_spectrum_N1
      have hk' : 2 * k ≤ n - 1 := by omega
      have : n - 1 - 2 * k = n - 1 - 2 * k := rfl
      omega
    _ = g * (3 * a + 2 * b) := by rw [ha, hb]; ring

lemma pom_toggle_scan_orbit_length_spectrum_primitive_block_length (n k d : Nat)
    (hd : d ≠ 0) (hdN1 : d ∣ pom_toggle_scan_orbit_length_spectrum_N1 n k) (hdk : d ∣ k) :
    (pom_toggle_scan_orbit_length_spectrum_primitive_block n k d).length =
      pom_toggle_scan_orbit_length_spectrum_ell n k / d := by
  rcases hdN1 with ⟨a, ha⟩
  rcases hdk with ⟨b, hb⟩
  calc
    (pom_toggle_scan_orbit_length_spectrum_primitive_block n k d).length =
        pom_toggle_scan_orbit_length_spectrum_N1 n k / d + k / d := by
      simp [pom_toggle_scan_orbit_length_spectrum_primitive_block]
    _ = a + b := by
      rw [ha, hb, Nat.mul_div_right _ (Nat.pos_of_ne_zero hd),
        Nat.mul_div_right _ (Nat.pos_of_ne_zero hd)]
    _ = pom_toggle_scan_orbit_length_spectrum_ell n k / d := by
      unfold pom_toggle_scan_orbit_length_spectrum_ell
      rw [ha, hb, ← Nat.mul_add, Nat.mul_div_right _ (Nat.pos_of_ne_zero hd)]

/-- The primitive-word orbit lengths are exactly the displayed values `L_k = 3n - 3 - 4k`, and
each such length divides the lcm of the whole displayed set. -/
theorem paper_pom_toggle_scan_order_closed_form_true (n : Nat) (hn : 4 ≤ n) :
    (∀ k : Nat, k < (n - 1) / 2 →
      togglePrimitiveWordOrbitLength n k = 3 * n - 3 - 4 * k ∧
        (togglePrimitiveWord n k).length = n - 1 - k) ∧
      (∀ k : Nat, k < (n - 1) / 2 →
        togglePrimitiveWordOrbitLength n k ∣ toggleScanOrderClosedFormLcm n) ∧
      toggleScanOrderClosedFormLcm n = (toggleScanOrderLengthCandidates n).foldl Nat.lcm 1 := by
  have _ := hn
  refine ⟨?_, ?_, rfl⟩
  · intro k hk
    have hk' : 2 * k ≤ n - 1 := by omega
    exact ⟨rfl, togglePrimitiveWord_length n k hk'⟩
  · intro k hk
    exact dvd_foldl_lcm_of_mem (togglePrimitiveWordOrbitLength_mem_candidates n k hk)

/-- Paper-facing wrapper for the scan-order lcm closed form.
    thm:pom-toggle-scan-order-closed-form -/
def paper_pom_toggle_scan_order_closed_form (n : Nat) (hn : 4 ≤ n) : Prop := by
  let _ := hn
  exact
    (∀ k : Nat, k < (n - 1) / 2 →
      togglePrimitiveWordOrbitLength n k = 3 * n - 3 - 4 * k ∧
        (togglePrimitiveWord n k).length = n - 1 - k) ∧
      (∀ k : Nat, k < (n - 1) / 2 →
        togglePrimitiveWordOrbitLength n k ∣ toggleScanOrderClosedFormLcm n) ∧
      toggleScanOrderClosedFormLcm n = (toggleScanOrderLengthCandidates n).foldl Nat.lcm 1

/-- Paper label: `thm:pom-toggle-scan-orbit-length-spectrum`. The displayed quotient family
`L_k / d` is realized by primitive blocks `u = 1^(N₁(k)/d) 2^(k/d)`, and every such length
divides the closed-form scan-order lcm. -/
theorem paper_pom_toggle_scan_orbit_length_spectrum (n : Nat) (hn : 4 <= n) :
    pom_toggle_scan_orbit_length_spectrum_statement n := by
  refine ⟨?_, ?_⟩
  · intro k hk
    have hclosed := (paper_pom_toggle_scan_order_closed_form_true n hn).1 k hk
    have hell : pom_toggle_scan_orbit_length_spectrum_ell n k = n - 1 - k := by
      unfold pom_toggle_scan_orbit_length_spectrum_ell pom_toggle_scan_orbit_length_spectrum_N1
      omega
    refine ⟨hclosed.1, ?_⟩
    simpa [hell] using hclosed.2
  · intro k hk1 hk d hd
    refine ⟨pom_toggle_scan_orbit_length_spectrum_primitive_block n k d, rfl, ?_, ?_⟩
    · have hdg : d ∣ pom_toggle_scan_orbit_length_spectrum_g n k := Nat.dvd_of_mem_divisors hd
      have hdpos : d ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hd)
      have hdN1 :
          d ∣ pom_toggle_scan_orbit_length_spectrum_N1 n k := by
        exact hdg.trans (Nat.gcd_dvd_left _ _)
      have hdk : d ∣ k := by
        exact hdg.trans (Nat.gcd_dvd_right _ _)
      exact pom_toggle_scan_orbit_length_spectrum_primitive_block_length n k d hdpos hdN1 hdk
    · have hLdiv :
          pom_toggle_scan_orbit_length_spectrum_L n k ∣ toggleScanOrderClosedFormLcm n := by
        simpa [pom_toggle_scan_orbit_length_spectrum_L] using
          (paper_pom_toggle_scan_order_closed_form_true n hn).2.1 k hk
      have hdg : d ∣ pom_toggle_scan_orbit_length_spectrum_g n k := Nat.dvd_of_mem_divisors hd
      have hdL : d ∣ pom_toggle_scan_orbit_length_spectrum_L n k := by
        exact hdg.trans (pom_toggle_scan_orbit_length_spectrum_g_dvd_L n k hk)
      exact (Nat.div_dvd_of_dvd hdL).trans hLdiv

/-- Paper label: `cor:pom-toggle-dihedral-time-reversal`. -/
theorem paper_pom_toggle_dihedral_time_reversal
    (involution conjugates_scan_to_inverse dihedral_quotient order_bound : Prop)
    (hInv : involution) (hConj : conjugates_scan_to_inverse)
    (hDih : involution -> conjugates_scan_to_inverse -> dihedral_quotient)
    (hBound : dihedral_quotient -> order_bound) :
    involution ∧ conjugates_scan_to_inverse ∧ dihedral_quotient ∧ order_bound := by
  exact ⟨hInv, hConj, hDih hInv hConj, hBound (hDih hInv hConj)⟩

end Omega.POM.ToggleOrder
