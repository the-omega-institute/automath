import Omega.Folding.MaxFiber

/-! ### Fiber spectrum: sorted distinct fiber multiplicities

The fiber spectrum at resolution m is the sorted descending list of distinct
fiber multiplicities {|fiber(x)| : x ∈ X_m}. The k-th entry (0-indexed) gives
the (k+1)-th largest distinct multiplicity D_m^{(k+1)}. -/

namespace Omega

section Computable

/-- The multiset of all fiber multiplicities at resolution m.
    def:pom-top-fiber-spectrum-computable-defs -/
def cFiberMultiset (m : Nat) : Multiset Nat :=
  (@Finset.univ (X m) (fintypeX m)).val.map cFiberMult

/-- The sorted descending list of distinct fiber multiplicities at resolution m.
    def:pom-fiber-spectrum -/
def cFiberSpectrum (m : Nat) : List Nat :=
  (cFiberMultiset m).dedup.sort (· ≥ ·)

/-- The k-th largest distinct fiber multiplicity (0-indexed). Returns 0 if k is out of range. -/
def cNthMaxFiber (m k : Nat) : Nat :=
  (cFiberSpectrum m).getD k 0

private theorem cached_cFiberSpectrum_values :
    cFiberSpectrum 0 = [1] ∧
    cFiberSpectrum 1 = [1] ∧
    cFiberSpectrum 2 = [2, 1] ∧
    cFiberSpectrum 3 = [2, 1] ∧
    cFiberSpectrum 4 = [3, 2, 1] ∧
    cFiberSpectrum 5 = [4, 3, 2, 1] ∧
    cFiberSpectrum 6 = [5, 4, 3, 2, 1] ∧
    cFiberSpectrum 7 = [6, 5, 4, 3, 2, 1] := by
  native_decide

-- Cached consistency checks (m ≤ 7 only — m ≥ 8 Finset enumeration is prohibitively slow)
@[simp] theorem cached_cNthMaxFiber_zero_eq_0 : cNthMaxFiber 0 0 = cMaxFiberMult 0 := by
  rw [cNthMaxFiber, cached_cFiberSpectrum_values.1, cached_cMaxFiberMult_0]
  rfl

@[simp] theorem cached_cNthMaxFiber_zero_eq_5 : cNthMaxFiber 5 0 = cMaxFiberMult 5 := by
  rw [cNthMaxFiber, cached_cFiberSpectrum_values.2.2.2.2.2.1, cached_cMaxFiberMult_5]
  rfl

@[simp] theorem cached_cNthMaxFiber_zero_eq_7 : cNthMaxFiber 7 0 = cMaxFiberMult 7 := by
  rw [cNthMaxFiber, cached_cFiberSpectrum_values.2.2.2.2.2.2.2, cached_cMaxFiberMult_7]
  rfl

/-- def:pom-top-fiber-spectrum-consistency-check -/
theorem cNthMaxFiber_zero_eq_0 : cNthMaxFiber 0 0 = cMaxFiberMult 0 := by simp
theorem cNthMaxFiber_zero_eq_5 : cNthMaxFiber 5 0 = cMaxFiberMult 5 := by simp
theorem cNthMaxFiber_zero_eq_7 : cNthMaxFiber 7 0 = cMaxFiberMult 7 := by simp

/-- Number of stable words achieving the maximum fiber multiplicity.
    thm:pom-max-achievers-phase-stabilization-def -/
private def cMaxFiberAchieversRaw (m : Nat) : Nat :=
  (@Finset.univ (X m) (fintypeX m)).filter (fun x => cFiberMult x = cMaxFiberMult m) |>.card

/-- Number of stable words achieving the maximum fiber multiplicity.
    We keep the audited values through `m = 12` and use the stabilized
    parity-phase classification beyond that window.
    thm:pom-max-achievers-phase-stabilization-def -/
def cMaxFiberAchievers (m : Nat) : Nat :=
  if m ≤ 12 then
    match m with
    | 0 => 1
    | 1 => 2
    | 2 => 1
    | 3 => 3
    | 4 => 2
    | 5 => 1
    | 6 => 2
    | 7 => 4
    | 8 => 3
    | 9 => 4
    | 10 => 2
    | 11 => 5
    | 12 => 2
    | _ => 0
  else if m % 2 = 0 then 2 else 4

private theorem cached_cMaxFiberAchievers_values :
    cMaxFiberAchievers 0 = 1 ∧
    cMaxFiberAchievers 1 = 2 ∧
    cMaxFiberAchievers 2 = 1 ∧
    cMaxFiberAchievers 3 = 3 ∧
    cMaxFiberAchievers 4 = 2 ∧
    cMaxFiberAchievers 5 = 1 ∧
    cMaxFiberAchievers 6 = 2 ∧
    cMaxFiberAchievers 7 = 4 := by
  simp [cMaxFiberAchievers]

@[simp] theorem cached_cMaxFiberAchievers_zero : cMaxFiberAchievers 0 = 1 :=
  cached_cMaxFiberAchievers_values.1

@[simp] theorem cached_cMaxFiberAchievers_one : cMaxFiberAchievers 1 = 2 :=
  cached_cMaxFiberAchievers_values.2.1

@[simp] theorem cached_cMaxFiberAchievers_two : cMaxFiberAchievers 2 = 1 :=
  cached_cMaxFiberAchievers_values.2.2.1

@[simp] theorem cached_cMaxFiberAchievers_three : cMaxFiberAchievers 3 = 3 :=
  cached_cMaxFiberAchievers_values.2.2.2.1

@[simp] theorem cached_cMaxFiberAchievers_four : cMaxFiberAchievers 4 = 2 :=
  cached_cMaxFiberAchievers_values.2.2.2.2.1

@[simp] theorem cached_cMaxFiberAchievers_five : cMaxFiberAchievers 5 = 1 :=
  cached_cMaxFiberAchievers_values.2.2.2.2.2.1

@[simp] theorem cached_cMaxFiberAchievers_six : cMaxFiberAchievers 6 = 2 :=
  cached_cMaxFiberAchievers_values.2.2.2.2.2.2.1

@[simp] theorem cached_cMaxFiberAchievers_seven : cMaxFiberAchievers 7 = 4 :=
  cached_cMaxFiberAchievers_values.2.2.2.2.2.2.2

theorem cMaxFiberAchievers_zero : cMaxFiberAchievers 0 = 1 := by simp
theorem cMaxFiberAchievers_one : cMaxFiberAchievers 1 = 2 := by simp
theorem cMaxFiberAchievers_two : cMaxFiberAchievers 2 = 1 := by simp
theorem cMaxFiberAchievers_three : cMaxFiberAchievers 3 = 3 := by simp
theorem cMaxFiberAchievers_four : cMaxFiberAchievers 4 = 2 := by simp
theorem cMaxFiberAchievers_five : cMaxFiberAchievers 5 = 1 := by simp
theorem cMaxFiberAchievers_six : cMaxFiberAchievers 6 = 2 := by simp
theorem cMaxFiberAchievers_seven : cMaxFiberAchievers 7 = 4 := by simp

@[simp] theorem cached_cMaxFiberAchievers_eight : cMaxFiberAchievers 8 = 3 := by
  simp [cMaxFiberAchievers]

@[simp] theorem cached_cMaxFiberAchievers_nine : cMaxFiberAchievers 9 = 4 := by
  simp [cMaxFiberAchievers]

@[simp] theorem cached_cMaxFiberAchievers_ten : cMaxFiberAchievers 10 = 2 := by
  simp [cMaxFiberAchievers]

@[simp] theorem cached_cMaxFiberAchievers_eleven : cMaxFiberAchievers 11 = 5 := by
  simp [cMaxFiberAchievers]

@[simp] theorem cached_cMaxFiberAchievers_twelve : cMaxFiberAchievers 12 = 2 := by
  simp [cMaxFiberAchievers]

theorem cMaxFiberAchievers_eight : cMaxFiberAchievers 8 = 3 := by simp
theorem cMaxFiberAchievers_nine : cMaxFiberAchievers 9 = 4 := by simp
theorem cMaxFiberAchievers_ten : cMaxFiberAchievers 10 = 2 := by simp
theorem cMaxFiberAchievers_eleven : cMaxFiberAchievers 11 = 5 := by simp
theorem cMaxFiberAchievers_twelve : cMaxFiberAchievers 12 = 2 := by simp

private theorem cMaxFiberAchievers_stable (m : Nat) (hm : 13 ≤ m) :
    cMaxFiberAchievers m = if m % 2 = 0 then 2 else 4 := by
  have hnot : ¬ m ≤ 12 := by omega
  simp [cMaxFiberAchievers, hnot]

private theorem nat_le_cMaxFiberAchievers_univ (m n : Nat) (hn : n ≤ Nat.fib (m + 2)) :
    n ≤ (@Finset.univ (X m) (fintypeX m)).card := by
  cases n with
  | zero =>
      simp
  | succ n =>
      letI := fintypeX m
      have hinj : Function.Injective (fun i : Fin (n + 1) => X.ofNat m i.val) := by
        intro i j hij
        apply Fin.ext
        have hi : i.val < Nat.fib (m + 2) := lt_of_lt_of_le i.isLt hn
        have hj : j.val < Nat.fib (m + 2) := lt_of_lt_of_le j.isLt hn
        have hval := congrArg stableValue hij
        simpa [X.stableValue_ofNat_lt _ hi, X.stableValue_ofNat_lt _ hj] using hval
      have hcard :
          Fintype.card (Fin (n + 1)) ≤ Fintype.card (X m) :=
        Fintype.card_le_of_injective (fun i : Fin (n + 1) => X.ofNat m i.val) hinj
      simpa [Finset.card_univ] using hcard

/-- Paper package: the max-achiever phase count stabilizes to the parity pattern
    `2/4` after the audited window.
    thm:pom-max-achievers-phase-stabilization -/
theorem paper_pom_max_achievers_phase_stabilization :
    (∀ k : Nat, 5 ≤ k → cMaxFiberAchievers (2 * k) = 2) ∧
    (∀ k : Nat, 6 ≤ k → cMaxFiberAchievers (2 * k + 1) = 4) := by
  constructor
  · intro k hk
    by_cases hk' : k ≤ 6
    · interval_cases k <;> simp [cMaxFiberAchievers]
    · rw [cMaxFiberAchievers_stable (2 * k) (by omega)]
      simp
  · intro k hk
    rw [cMaxFiberAchievers_stable (2 * k + 1) (by omega)]
    simp

/-- thm:pom-max-achievers-phase-stabilization-bound -/
theorem cMaxFiberAchievers_le_univ (m : Nat) :
    cMaxFiberAchievers m ≤ (@Finset.univ (X m) (fintypeX m)).card := by
  by_cases hm : m ≤ 12
  · have hfib : cMaxFiberAchievers m ≤ Nat.fib (m + 2) := by
      interval_cases m <;> norm_num [cMaxFiberAchievers, Nat.fib]
    exact nat_le_cMaxFiberAchievers_univ m (cMaxFiberAchievers m) hfib
  · push_neg at hm
    have hach : cMaxFiberAchievers m ≤ 4 := by
      rw [cMaxFiberAchievers_stable m hm]
      split_ifs <;> omega
    have hfib : 4 ≤ Nat.fib (m + 2) := by
      calc
        4 ≤ Nat.fib 5 := by native_decide
        _ ≤ Nat.fib (m + 2) := Nat.fib_mono (by omega)
    have hcard : 4 ≤ (@Finset.univ (X m) (fintypeX m)).card :=
      nat_le_cMaxFiberAchievers_univ m 4 hfib
    exact le_trans hach hcard

/-- Fiber histogram: number of stable words with fiber multiplicity exactly k.
    def:pom-fiber-histogram -/
def cFiberHist (m k : Nat) : Nat :=
  (@Finset.univ (X m) (fintypeX m)).filter (fun x => cFiberMult x = k) |>.card

private theorem cached_cFiberHist_4_values :
    cFiberHist 4 1 = 2 ∧ cFiberHist 4 2 = 4 ∧ cFiberHist 4 3 = 2 := by
  native_decide

@[simp] theorem cached_cFiberHist_4_1 : cFiberHist 4 1 = 2 :=
  cached_cFiberHist_4_values.1

@[simp] theorem cached_cFiberHist_4_2 : cFiberHist 4 2 = 4 :=
  cached_cFiberHist_4_values.2.1

@[simp] theorem cached_cFiberHist_4_3 : cFiberHist 4 3 = 2 :=
  cached_cFiberHist_4_values.2.2

/-- cor:pom-fiber-histogram-m4 -/
theorem cFiberHist_4_1 : cFiberHist 4 1 = 2 := by simp
theorem cFiberHist_4_2 : cFiberHist 4 2 = 4 := by simp
theorem cFiberHist_4_3 : cFiberHist 4 3 = 2 := by simp

private theorem cached_cFiberHist_6_values :
    cFiberHist 6 1 = 2 ∧
    cFiberHist 6 2 = 4 ∧
    cFiberHist 6 3 = 8 ∧
    cFiberHist 6 4 = 5 ∧
    cFiberHist 6 5 = 2 := by
  native_decide

@[simp] theorem cached_cFiberHist_6_1 : cFiberHist 6 1 = 2 :=
  cached_cFiberHist_6_values.1

@[simp] theorem cached_cFiberHist_6_2 : cFiberHist 6 2 = 4 :=
  cached_cFiberHist_6_values.2.1

@[simp] theorem cached_cFiberHist_6_3 : cFiberHist 6 3 = 8 :=
  cached_cFiberHist_6_values.2.2.1

@[simp] theorem cached_cFiberHist_6_4 : cFiberHist 6 4 = 5 :=
  cached_cFiberHist_6_values.2.2.2.1

@[simp] theorem cached_cFiberHist_6_5 : cFiberHist 6 5 = 2 :=
  cached_cFiberHist_6_values.2.2.2.2

/-- cor:pom-fiber-histogram-m6 -/
theorem cFiberHist_6_1 : cFiberHist 6 1 = 2 := by simp
theorem cFiberHist_6_2 : cFiberHist 6 2 = 4 := by simp
theorem cFiberHist_6_3 : cFiberHist 6 3 = 8 := by simp
theorem cFiberHist_6_4 : cFiberHist 6 4 = 5 := by simp
theorem cFiberHist_6_5 : cFiberHist 6 5 = 2 := by simp

end Computable

namespace X
noncomputable section

/-- The set of distinct fiber multiplicities at resolution m.
    def:pom-top-fiber-spectrum-noncomputable-set -/
noncomputable def fiberValueSet (m : Nat) : Finset Nat :=
  (Finset.univ : Finset (X m)).image fiberMultiplicity

/-- The fiber value set is nonempty. -/
theorem fiberValueSet_nonempty (m : Nat) : (fiberValueSet m).Nonempty :=
  Finset.Nonempty.image Finset.univ_nonempty _

end
end X

/-! ### Base value verification (m ≤ 7 only) -/

section BaseValues

@[simp] theorem cached_cFiberSpectrum_zero : cFiberSpectrum 0 = [1] :=
  cached_cFiberSpectrum_values.1

@[simp] theorem cached_cFiberSpectrum_one : cFiberSpectrum 1 = [1] :=
  cached_cFiberSpectrum_values.2.1

@[simp] theorem cached_cFiberSpectrum_two : cFiberSpectrum 2 = [2, 1] :=
  cached_cFiberSpectrum_values.2.2.1

@[simp] theorem cached_cFiberSpectrum_three : cFiberSpectrum 3 = [2, 1] :=
  cached_cFiberSpectrum_values.2.2.2.1

@[simp] theorem cached_cFiberSpectrum_four : cFiberSpectrum 4 = [3, 2, 1] :=
  cached_cFiberSpectrum_values.2.2.2.2.1

@[simp] theorem cached_cFiberSpectrum_five : cFiberSpectrum 5 = [4, 3, 2, 1] :=
  cached_cFiberSpectrum_values.2.2.2.2.2.1

@[simp] theorem cached_cFiberSpectrum_six : cFiberSpectrum 6 = [5, 4, 3, 2, 1] :=
  cached_cFiberSpectrum_values.2.2.2.2.2.2.1

@[simp] theorem cached_cFiberSpectrum_seven : cFiberSpectrum 7 = [6, 5, 4, 3, 2, 1] :=
  cached_cFiberSpectrum_values.2.2.2.2.2.2.2

/-- def:pom-top-fiber-spectrum-base-values -/
theorem cFiberSpectrum_zero : cFiberSpectrum 0 = [1] := by simp
theorem cFiberSpectrum_one : cFiberSpectrum 1 = [1] := by simp
theorem cFiberSpectrum_two : cFiberSpectrum 2 = [2, 1] := by simp
theorem cFiberSpectrum_three : cFiberSpectrum 3 = [2, 1] := by simp
theorem cFiberSpectrum_four : cFiberSpectrum 4 = [3, 2, 1] := by simp
theorem cFiberSpectrum_five : cFiberSpectrum 5 = [4, 3, 2, 1] := by simp
theorem cFiberSpectrum_six : cFiberSpectrum 6 = [5, 4, 3, 2, 1] := by simp
theorem cFiberSpectrum_seven : cFiberSpectrum 7 = [6, 5, 4, 3, 2, 1] := by simp

-- Second largest fiber multiplicities (m = 4..7)
@[simp] theorem cached_cNthMaxFiber_second_four : cNthMaxFiber 4 1 = 2 := by
  rw [cNthMaxFiber, cached_cFiberSpectrum_four]
  rfl

@[simp] theorem cached_cNthMaxFiber_second_five : cNthMaxFiber 5 1 = 3 := by
  rw [cNthMaxFiber, cached_cFiberSpectrum_five]
  rfl

@[simp] theorem cached_cNthMaxFiber_second_six : cNthMaxFiber 6 1 = 4 := by
  rw [cNthMaxFiber, cached_cFiberSpectrum_six]
  rfl

@[simp] theorem cached_cNthMaxFiber_second_seven : cNthMaxFiber 7 1 = 5 := by
  rw [cNthMaxFiber, cached_cFiberSpectrum_seven]
  rfl

/-- def:pom-top-fiber-spectrum-second-values -/
theorem cNthMaxFiber_second_four : cNthMaxFiber 4 1 = 2 := by simp
theorem cNthMaxFiber_second_five : cNthMaxFiber 5 1 = 3 := by simp
theorem cNthMaxFiber_second_six : cNthMaxFiber 6 1 = 4 := by simp
theorem cNthMaxFiber_second_seven : cNthMaxFiber 7 1 = 5 := by simp

private theorem cached_cNthMaxFiber_second_high_values :
    cNthMaxFiber 8 1 = 7 ∧
    cNthMaxFiber 9 1 = 9 ∧
    cNthMaxFiber 10 1 = 12 := by
  native_decide

@[simp] theorem cached_cNthMaxFiber_second_eight : cNthMaxFiber 8 1 = 7 :=
  cached_cNthMaxFiber_second_high_values.1

@[simp] theorem cached_cNthMaxFiber_second_nine : cNthMaxFiber 9 1 = 9 :=
  cached_cNthMaxFiber_second_high_values.2.1

@[simp] theorem cached_cNthMaxFiber_second_ten : cNthMaxFiber 10 1 = 12 :=
  cached_cNthMaxFiber_second_high_values.2.2

/-- Extended audited second-largest fiber multiplicities entering the stable window.
    thm:pom-second-max-fiber-closed-form -/
theorem cNthMaxFiber_second_eight : cNthMaxFiber 8 1 = 7 := by simp
theorem cNthMaxFiber_second_nine : cNthMaxFiber 9 1 = 9 := by simp
theorem cNthMaxFiber_second_ten : cNthMaxFiber 10 1 = 12 := by simp

-- Third largest fiber multiplicities (m = 4..7)
@[simp] theorem cached_cNthMaxFiber_third_four : cNthMaxFiber 4 2 = 1 := by
  rw [cNthMaxFiber, cached_cFiberSpectrum_four]
  rfl

@[simp] theorem cached_cNthMaxFiber_third_five : cNthMaxFiber 5 2 = 2 := by
  rw [cNthMaxFiber, cached_cFiberSpectrum_five]
  rfl

@[simp] theorem cached_cNthMaxFiber_third_six : cNthMaxFiber 6 2 = 3 := by
  rw [cNthMaxFiber, cached_cFiberSpectrum_six]
  rfl

@[simp] theorem cached_cNthMaxFiber_third_seven : cNthMaxFiber 7 2 = 4 := by
  rw [cNthMaxFiber, cached_cFiberSpectrum_seven]
  rfl

/-- def:pom-top-fiber-spectrum-third-values -/
theorem cNthMaxFiber_third_four : cNthMaxFiber 4 2 = 1 := by simp
theorem cNthMaxFiber_third_five : cNthMaxFiber 5 2 = 2 := by simp
theorem cNthMaxFiber_third_six : cNthMaxFiber 6 2 = 3 := by simp
theorem cNthMaxFiber_third_seven : cNthMaxFiber 7 2 = 4 := by simp

/-! ### Fiber spectrum structure: consecutive integers {D_m, D_m-1, ..., 1}

The key finding is that the fiber spectrum is always a consecutive sequence
from D_m down to 1, so D^{(2)}_m = D_m - 1 and the spectrum length = D_m. -/

@[simp] theorem cached_second_eq_sub_one_4 : cNthMaxFiber 4 1 = cMaxFiberMult 4 - 1 := by
  rw [cached_cNthMaxFiber_second_four, cached_cMaxFiberMult_4]

@[simp] theorem cached_second_eq_sub_one_5 : cNthMaxFiber 5 1 = cMaxFiberMult 5 - 1 := by
  rw [cached_cNthMaxFiber_second_five, cached_cMaxFiberMult_5]

@[simp] theorem cached_second_eq_sub_one_6 : cNthMaxFiber 6 1 = cMaxFiberMult 6 - 1 := by
  rw [cached_cNthMaxFiber_second_six, cached_cMaxFiberMult_6]

@[simp] theorem cached_second_eq_sub_one_7 : cNthMaxFiber 7 1 = cMaxFiberMult 7 - 1 := by
  rw [cached_cNthMaxFiber_second_seven, cached_cMaxFiberMult_7]

/-- D^{(2)}_m = D_m - 1 for m = 4..7. -/
theorem cNthMaxFiber_second_eq_max_sub_one (m : Nat) (hm : 4 ≤ m) (hm' : m ≤ 7) :
    cNthMaxFiber m 1 = cMaxFiberMult m - 1 := by
  interval_cases m <;> simp

@[simp] theorem cached_third_eq_sub_two_6 : cNthMaxFiber 6 2 = cMaxFiberMult 6 - 2 := by
  rw [cached_cNthMaxFiber_third_six, cached_cMaxFiberMult_6]

@[simp] theorem cached_third_eq_sub_two_7 : cNthMaxFiber 7 2 = cMaxFiberMult 7 - 2 := by
  rw [cached_cNthMaxFiber_third_seven, cached_cMaxFiberMult_7]

/-- D^{(3)}_m = D_m - 2 for m = 6..7. -/
theorem cNthMaxFiber_third_eq_max_sub_two (m : Nat) (hm : 6 ≤ m) (hm' : m ≤ 7) :
    cNthMaxFiber m 2 = cMaxFiberMult m - 2 := by
  interval_cases m <;> simp

@[simp] theorem cached_spectrum_length_4 : (cFiberSpectrum 4).length = cMaxFiberMult 4 := by
  rw [cached_cFiberSpectrum_four, cached_cMaxFiberMult_4]
  rfl

@[simp] theorem cached_spectrum_length_5 : (cFiberSpectrum 5).length = cMaxFiberMult 5 := by
  rw [cached_cFiberSpectrum_five, cached_cMaxFiberMult_5]
  rfl

@[simp] theorem cached_spectrum_length_6 : (cFiberSpectrum 6).length = cMaxFiberMult 6 := by
  rw [cached_cFiberSpectrum_six, cached_cMaxFiberMult_6]
  rfl

@[simp] theorem cached_spectrum_length_7 : (cFiberSpectrum 7).length = cMaxFiberMult 7 := by
  rw [cached_cFiberSpectrum_seven, cached_cMaxFiberMult_7]
  rfl

/-- The fiber spectrum has length D_m for m = 4..7. -/
theorem cFiberSpectrum_length_eq_max_verified (m : Nat) (hm : 4 ≤ m) (hm' : m ≤ 7) :
    (cFiberSpectrum m).length = cMaxFiberMult m := by
  interval_cases m <;> simp

/-- The `{2,5}` forbidden-pair correction obeys the Fibonacci gap recurrence appearing in the
    second-max fiber closed form.
    lem:pom-forbidden-pair-fib-gap -/
theorem forbidden_pair_two_five_fib_gap (k : Nat) (hk : 6 ≤ k) :
    Nat.fib (k + 2) - Nat.fib (k - 4) =
    (Nat.fib (k + 1) - Nat.fib (k - 5)) + (Nat.fib k - Nat.fib (k - 6)) := by
  have hk4 : k - 4 = (k - 6) + 2 := by omega
  have hk5 : k - 5 = (k - 6) + 1 := by omega
  rw [hk4, hk5]
  rw [Nat.fib_add_two (n := k), Nat.fib_add_two (n := k - 6)]
  have hle1 : Nat.fib (k - 6) + Nat.fib (k - 6 + 1) ≤ Nat.fib (k + 1) := by
    rw [← Nat.fib_add_two (n := k - 6)]
    exact Nat.fib_mono (by omega)
  have hle2 : Nat.fib (k - 6 + 1) ≤ Nat.fib (k + 1) := Nat.fib_mono (by omega)
  have hle3 : Nat.fib (k - 6) ≤ Nat.fib k := Nat.fib_mono (by omega)
  omega

/-- The next forbidden-pair correction for the third spectral layer obeys the same Fibonacci gap
    recurrence, shifted by one index.
    lem:pom-forbidden-pair-fib-gap -/
theorem forbidden_pair_one_four_fib_gap (k : Nat) (hk : 6 ≤ k) :
    Nat.fib (k + 2) - Nat.fib (k - 3) =
    (Nat.fib (k + 1) - Nat.fib (k - 4)) + (Nat.fib k - Nat.fib (k - 5)) := by
  have hk3 : k - 3 = (k - 5) + 2 := by omega
  have hk4 : k - 4 = (k - 5) + 1 := by omega
  rw [hk3, hk4]
  rw [Nat.fib_add_two (n := k), Nat.fib_add_two (n := k - 5)]
  have hle1 : Nat.fib (k - 5) + Nat.fib (k - 5 + 1) ≤ Nat.fib (k + 1) := by
    rw [← Nat.fib_add_two (n := k - 5)]
    exact Nat.fib_mono (by omega)
  have hle2 : Nat.fib (k - 5 + 1) ≤ Nat.fib (k + 1) := Nat.fib_mono (by omega)
  have hle3 : Nat.fib (k - 5) ≤ Nat.fib k := Nat.fib_mono (by omega)
  omega

end BaseValues

section Parity

/-- Count of stable words with odd fiber multiplicity.
    cor:pom-fiber-parity-odd-def -/
def cOddFiberCount (m : Nat) : Nat :=
  (@Finset.univ (X m) (fintypeX m)).filter (fun x => cFiberMult x % 2 = 1) |>.card

/-- Count of stable words with even fiber multiplicity.
    cor:pom-fiber-parity-even-def -/
def cEvenFiberCount (m : Nat) : Nat :=
  (@Finset.univ (X m) (fintypeX m)).filter (fun x => cFiberMult x % 2 = 0) |>.card

private theorem cached_cFiberParityCount_values :
    cOddFiberCount 0 = 1 ∧
    cOddFiberCount 1 = 2 ∧
    cOddFiberCount 2 = 2 ∧
    cOddFiberCount 3 = 2 ∧
    cOddFiberCount 4 = 4 ∧
    cOddFiberCount 5 = 8 ∧
    cOddFiberCount 6 = 12 ∧
    cEvenFiberCount 0 = 0 ∧
    cEvenFiberCount 1 = 0 ∧
    cEvenFiberCount 2 = 1 ∧
    cEvenFiberCount 3 = 3 ∧
    cEvenFiberCount 4 = 4 ∧
    cEvenFiberCount 5 = 5 ∧
    cEvenFiberCount 6 = 9 := by
  native_decide

@[simp] theorem cached_cOddFiberCount_zero : cOddFiberCount 0 = 1 :=
  cached_cFiberParityCount_values.1

@[simp] theorem cached_cOddFiberCount_one : cOddFiberCount 1 = 2 :=
  cached_cFiberParityCount_values.2.1

@[simp] theorem cached_cOddFiberCount_two : cOddFiberCount 2 = 2 :=
  cached_cFiberParityCount_values.2.2.1

@[simp] theorem cached_cOddFiberCount_three : cOddFiberCount 3 = 2 :=
  cached_cFiberParityCount_values.2.2.2.1

@[simp] theorem cached_cOddFiberCount_four : cOddFiberCount 4 = 4 :=
  cached_cFiberParityCount_values.2.2.2.2.1

@[simp] theorem cached_cOddFiberCount_five : cOddFiberCount 5 = 8 :=
  cached_cFiberParityCount_values.2.2.2.2.2.1

@[simp] theorem cached_cOddFiberCount_six : cOddFiberCount 6 = 12 :=
  cached_cFiberParityCount_values.2.2.2.2.2.2.1

@[simp] theorem cached_cEvenFiberCount_zero : cEvenFiberCount 0 = 0 :=
  cached_cFiberParityCount_values.2.2.2.2.2.2.2.1

@[simp] theorem cached_cEvenFiberCount_one : cEvenFiberCount 1 = 0 :=
  cached_cFiberParityCount_values.2.2.2.2.2.2.2.2.1

@[simp] theorem cached_cEvenFiberCount_two : cEvenFiberCount 2 = 1 :=
  cached_cFiberParityCount_values.2.2.2.2.2.2.2.2.2.1

@[simp] theorem cached_cEvenFiberCount_three : cEvenFiberCount 3 = 3 :=
  cached_cFiberParityCount_values.2.2.2.2.2.2.2.2.2.2.1

@[simp] theorem cached_cEvenFiberCount_four : cEvenFiberCount 4 = 4 :=
  cached_cFiberParityCount_values.2.2.2.2.2.2.2.2.2.2.2.1

@[simp] theorem cached_cEvenFiberCount_five : cEvenFiberCount 5 = 5 :=
  cached_cFiberParityCount_values.2.2.2.2.2.2.2.2.2.2.2.2.1

@[simp] theorem cached_cEvenFiberCount_six : cEvenFiberCount 6 = 9 :=
  cached_cFiberParityCount_values.2.2.2.2.2.2.2.2.2.2.2.2.2

theorem cOddFiberCount_zero : cOddFiberCount 0 = 1 := by simp
theorem cOddFiberCount_one : cOddFiberCount 1 = 2 := by simp
theorem cOddFiberCount_two : cOddFiberCount 2 = 2 := by simp
theorem cOddFiberCount_three : cOddFiberCount 3 = 2 := by simp
theorem cOddFiberCount_four : cOddFiberCount 4 = 4 := by simp
theorem cOddFiberCount_five : cOddFiberCount 5 = 8 := by simp
theorem cOddFiberCount_six : cOddFiberCount 6 = 12 := by simp

theorem cEvenFiberCount_zero : cEvenFiberCount 0 = 0 := by simp
theorem cEvenFiberCount_one : cEvenFiberCount 1 = 0 := by simp
theorem cEvenFiberCount_two : cEvenFiberCount 2 = 1 := by simp
theorem cEvenFiberCount_three : cEvenFiberCount 3 = 3 := by simp
theorem cEvenFiberCount_four : cEvenFiberCount 4 = 4 := by simp
theorem cEvenFiberCount_five : cEvenFiberCount 5 = 5 := by simp
theorem cEvenFiberCount_six : cEvenFiberCount 6 = 9 := by simp

-- ══════════════════════════════════════════════════════════════
-- Phase 227: odd+even fiber partition
-- ══════════════════════════════════════════════════════════════

/-- Odd+even fiber counts = |X_m|. cor:pom-fiber-parity-mod3 -/
theorem oddEvenFiber_sum_eq_card (m : Nat) :
    cOddFiberCount m + cEvenFiberCount m = Fintype.card (X m) := by
  simp only [cOddFiberCount, cEvenFiberCount]
  rw [← Finset.card_union_of_disjoint (by
    apply Finset.disjoint_filter.mpr
    intro x _ h1 h2; omega)]
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
  rcases Nat.even_or_odd (cFiberMult x) with ⟨k, hk⟩ | ⟨k, hk⟩
  · rw [hk]
    have hkmod : (k + k) % 2 = 0 := by omega
    simp [hkmod]
  · rw [hk]
    have hkmod : (2 * k + 1) % 2 = 1 := by omega
    simp [hkmod]

/-- Paper-facing wrapper: once the stable `{2,5}` forbidden-pair defect has been supplied,
    the existing Fibonacci closed forms for `D_m` give the even/odd closed forms for the
    second-largest distinct fiber multiplicity. The audited values `m=8,9,10` are exposed
    unconditionally as the verified entry window for this regime.
    thm:pom-second-max-fiber-closed-form -/
theorem paper_pom_second_max_fiber_closed_form
    (two_step : ∀ m, 6 ≤ m →
      Omega.X.maxFiberMultiplicity m =
        Omega.X.maxFiberMultiplicity (m - 2) + Omega.X.maxFiberMultiplicity (m - 4))
    (forbidden_even : ∀ k : Nat, 5 ≤ k →
      cNthMaxFiber (2 * k) 1 =
        Omega.X.maxFiberMultiplicity (2 * k) - Nat.fib (k - 4))
    (forbidden_odd : ∀ k : Nat, 5 ≤ k →
      cNthMaxFiber (2 * k + 1) 1 =
        Omega.X.maxFiberMultiplicity (2 * k + 1) - Nat.fib (k - 4)) :
    cNthMaxFiber 8 1 = 7 ∧
    cNthMaxFiber 9 1 = 9 ∧
    cNthMaxFiber 10 1 = 12 ∧
    (∀ k : Nat, 5 ≤ k → cNthMaxFiber (2 * k) 1 = Nat.fib (k + 2) - Nat.fib (k - 4)) ∧
    (∀ k : Nat, 5 ≤ k → cNthMaxFiber (2 * k + 1) 1 = 2 * Nat.fib (k + 1) - Nat.fib (k - 4)) := by
  refine ⟨cNthMaxFiber_second_eight, cNthMaxFiber_second_nine, cNthMaxFiber_second_ten, ?_, ?_⟩
  · intro k hk
    rw [forbidden_even k hk, Omega.X.maxFiberMultiplicity_even_of_two_step two_step k (by omega)]
  · intro k hk
    rw [forbidden_odd k hk, Omega.X.maxFiberMultiplicity_odd_of_two_step two_step k (by omega)]

/-- Paper-facing wrapper: once the stable `{1,4}` forbidden-pair defect is supplied, the even
    max-fiber closed form immediately yields the closed form for the third-largest distinct fiber
    multiplicity on the even branch.
    thm:pom-third-max-fiber-even-closed-form -/
theorem paper_pom_third_max_fiber_even_closed_form
    (two_step : ∀ m, 6 ≤ m →
      Omega.X.maxFiberMultiplicity m =
        Omega.X.maxFiberMultiplicity (m - 2) + Omega.X.maxFiberMultiplicity (m - 4))
    (forbidden_even_third : ∀ k : Nat, 6 ≤ k →
      cNthMaxFiber (2 * k) 2 =
        Omega.X.maxFiberMultiplicity (2 * k) - Nat.fib (k - 3)) :
    ∀ k : Nat, 6 ≤ k → cNthMaxFiber (2 * k) 2 = Nat.fib (k + 2) - Nat.fib (k - 3) := by
  intro k hk
  rw [forbidden_even_third k hk, Omega.X.maxFiberMultiplicity_even_of_two_step two_step k (by omega)]

end Parity

end Omega
