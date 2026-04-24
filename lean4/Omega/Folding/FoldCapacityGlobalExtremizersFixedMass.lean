import Mathlib

namespace Omega.Folding

open scoped BigOperators

/-- The integer-threshold capacity curve of a finite spectrum. -/
def foldNatCapacityCurve {N : ℕ} (d : Fin N → ℕ) (T : ℕ) : ℕ :=
  ∑ i, Nat.min (d i) T

/-- Positive integer spectra of length `N` and total mass `M`. -/
def fixedMassPositiveSpectrum (N M : ℕ) (d : Fin N → ℕ) : Prop :=
  (∀ i, 1 ≤ d i) ∧ ∑ i, d i = M

/-- The excess profile of the spike extremizer above the forced baseline `1`. -/
def spikeExcess (N E : ℕ) (i : Fin N) : ℕ :=
  if i.1 = 0 then E else 0

/-- The spike spectrum with one large entry and `N - 1` unit entries. -/
def spikeSpectrum (N M : ℕ) (i : Fin N) : ℕ :=
  spikeExcess N (M - N) i + 1

/-- The balanced excess profile for the leftover mass `E = M - N`. -/
def balancedExcess (N E : ℕ) (i : Fin N) : ℕ :=
  E / N + if i.1 < E % N then 1 else 0

/-- The balanced spectrum: entries differ by at most `1`. -/
def balancedSpectrum (N M : ℕ) (i : Fin N) : ℕ :=
  balancedExcess N (M - N) i + 1

/-- Fixed-mass global extremizers for the discrete capacity curve. -/
def foldCapacityGlobalExtremizersFixedMass (N M : ℕ) : Prop :=
  ∀ d : Fin N → ℕ, fixedMassPositiveSpectrum N M d →
    (∀ T : ℕ, foldNatCapacityCurve (spikeSpectrum N M) T ≤ foldNatCapacityCurve d T) ∧
      (∀ T : ℕ, foldNatCapacityCurve d T ≤ foldNatCapacityCurve (balancedSpectrum N M) T)

private lemma min_add_le_add_min (a b T : ℕ) : min (a + b) T ≤ min a T + min b T := by
  by_cases ha : T ≤ a
  · rw [Nat.min_eq_right ha]
    omega
  · have ha' : a < T := lt_of_not_ge ha
    rw [Nat.min_eq_left ha'.le]
    by_cases hab : T ≤ a + b
    · have hsub : T - a ≤ Nat.min b T := by
        refine le_min ?_ (Nat.sub_le _ _)
        omega
      omega
    · have hab' : a + b < T := lt_of_not_ge hab
      rw [Nat.min_eq_left hab'.le]
      omega

private lemma min_sum_le_sum_min {α : Type*} [DecidableEq α] (s : Finset α) (a : α → ℕ) (T : ℕ) :
    min (Finset.sum s a) T ≤ Finset.sum s (fun x => min (a x) T) := by
  induction s using Finset.induction with
  | empty =>
      simp
  | @insert x s hx ih =>
      rw [Finset.sum_insert hx, Finset.sum_insert hx]
      have hstep :
          Nat.min (a x) T + Nat.min (Finset.sum s a) T ≤
            Nat.min (a x) T + Finset.sum s (fun y => Nat.min (a y) T) := by
        gcongr
      exact (min_add_le_add_min (a x) (Finset.sum s a) T).trans hstep

private lemma sum_min_le_card_mul {N : ℕ} (e : Fin N → ℕ) (T : ℕ) :
    (∑ i, min (e i) T) ≤ N * T := by
  calc
    (∑ i, Nat.min (e i) T) ≤ ∑ i : Fin N, T := by
      refine Finset.sum_le_sum ?_
      intro i hi
      exact Nat.min_le_right _ _
    _ = N * T := by simp

private lemma capacity_succ_eq_baseline_plus_excess {N : ℕ} (d : Fin N → ℕ) (T : ℕ)
    (hpos : ∀ i, 1 ≤ d i) :
    foldNatCapacityCurve d (T + 1) = N + ∑ i, min (d i - 1) T := by
  unfold foldNatCapacityCurve
  calc
    ∑ i : Fin N, min (d i) (T + 1) = ∑ i : Fin N, (1 + min (d i - 1) T) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      by_cases hdi : d i ≤ T
      · have hpred : d i - 1 ≤ T := by omega
        have hd1 : d i = (d i - 1) + 1 := by
          exact (Nat.sub_add_cancel (hpos i)).symm
        have hsuc : 1 + (d i - 1) ≤ T + 1 := by omega
        rw [hd1]
        simp [min_eq_left hsuc, min_eq_left hpred, add_comm]
      · have hdi' : T < d i := lt_of_not_ge hdi
        have hs : T + 1 ≤ d i := by omega
        have hpred : T ≤ d i - 1 := by omega
        simp [min_eq_right hs, min_eq_right hpred, add_comm]
    _ = ∑ i : Fin N, 1 + ∑ i : Fin N, min (d i - 1) T := by rw [Finset.sum_add_distrib]
    _ = N + ∑ i, min (d i - 1) T := by simp

private lemma sum_excess_eq {N M : ℕ} (d : Fin N → ℕ) (hpos : ∀ i, 1 ≤ d i) (hsum : ∑ i, d i = M) :
    ∑ i, (d i - 1) = M - N := by
  have hsplit : ∑ i, d i = ∑ i, ((d i - 1) + 1) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    exact (Nat.sub_add_cancel (hpos i)).symm
  rw [hsum] at hsplit
  rw [Finset.sum_add_distrib] at hsplit
  simp at hsplit
  omega

private lemma sum_indicator_range (N r : ℕ) (hr : r ≤ N) :
    Finset.sum (Finset.range N) (fun i => if i < r then 1 else 0) = r := by
  calc
    Finset.sum (Finset.range N) (fun i => if i < r then 1 else 0)
        = Finset.sum ((Finset.range N).filter (fun i => i < r)) (fun _ => 1) := by
            rw [Finset.sum_filter]
    _ = ((Finset.range N).filter (fun i => i < r)).card := by
          rw [Finset.card_eq_sum_ones]
    _ = (Finset.range r).card := by
          have hEq : (Finset.range N).filter (fun i => i < r) = Finset.range r := by
            ext i
            constructor
            · intro hi
              exact Finset.mem_range.mpr ((Finset.mem_filter.mp hi).2)
            · intro hi
              exact Finset.mem_filter.mpr
                ⟨Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hi) hr),
                  Finset.mem_range.mp hi⟩
          rw [hEq]
    _ = r := by simp

private lemma balancedExcess_sum (N E : ℕ) (hN : 0 < N) :
    ∑ i, balancedExcess N E i = E := by
  let q := E / N
  let r := E % N
  have hcount : Finset.sum (Finset.range N) (fun i => if i < r then 1 else 0) = r := by
    exact sum_indicator_range N r (by
      have hrlt : E % N < N := Nat.mod_lt _ hN
      exact le_of_lt hrlt)
  calc
    ∑ i, balancedExcess N E i = ∑ i : Fin N, (q + if i.1 < r then 1 else 0) := by
      simp [balancedExcess, q, r]
    _ = (∑ i : Fin N, q) + (∑ i : Fin N, (if i.1 < r then 1 else 0)) := by
          rw [Finset.sum_add_distrib]
    _ = N * q + r := by
      have hsumInd : (∑ i : Fin N, (if i.1 < r then 1 else 0)) = r := by
        exact (Fin.sum_univ_eq_sum_range (fun i : ℕ => if i < r then 1 else 0) N).trans hcount
      rw [hsumInd]
      simp
    _ = E := by
      have hdecomp : E % N + N * (E / N) = E := Nat.mod_add_div E N
      simpa [q, r, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm] using hdecomp
          
private lemma spikeExcess_sum {N : ℕ} (E : ℕ) (hN : 0 < N) :
    ∑ i, spikeExcess N E i = E := by
  let i0 : Fin N := ⟨0, hN⟩
  rw [Finset.sum_eq_single i0]
  · simp [spikeExcess, i0]
  · intro i hi hne
    have hi0 : i.1 ≠ 0 := by
      intro hiz
      apply hne
      apply Fin.ext
      simpa [i0] using hiz
    simp [spikeExcess, hi0]
  · intro hi0
    simp at hi0

theorem spikeSpectrum_fixedMass (N M : ℕ) (hN : 0 < N) (hNM : N ≤ M) :
    fixedMassPositiveSpectrum N M (spikeSpectrum N M) := by
  constructor
  · intro i
    unfold spikeSpectrum spikeExcess
    split_ifs <;> omega
  · have hsumEx : ∑ i, spikeExcess N (M - N) i = M - N := spikeExcess_sum (M - N) hN
    calc
      ∑ i, spikeSpectrum N M i = ∑ i, (spikeExcess N (M - N) i + 1) := by rfl
      _ = ∑ i, spikeExcess N (M - N) i + ∑ i : Fin N, 1 := by rw [Finset.sum_add_distrib]
      _ = (M - N) + N := by simp [hsumEx]
      _ = M := by omega

private lemma balancedExcess_capacity (N E T : ℕ) (hN : 0 < N) :
    (∑ i, min (balancedExcess N E i) T) = min E (N * T) := by
  let q := E / N
  by_cases hT : T ≤ q
  · have hconst : ∀ i : Fin N, min (balancedExcess N E i) T = T := by
      intro i
      unfold balancedExcess
      have : T ≤ E / N := by simpa [q] using hT
      omega
    calc
      (∑ i, min (balancedExcess N E i) T) = ∑ i : Fin N, T := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        simpa using hconst i
      _ = N * T := by simp
      _ = min E (N * T) := by
        symm
        apply min_eq_right
        have hmul : N * T ≤ N * q := Nat.mul_le_mul_left _ hT
        have hqle : N * q ≤ E := by
          have hdecomp : E = N * q + E % N := by
            simpa [q, Nat.add_comm, Nat.mul_comm] using (Nat.mod_add_div E N).symm
          omega
        exact le_trans hmul hqle
  · have hq : q < T := lt_of_not_ge hT
    have hconst : ∀ i : Fin N, min (balancedExcess N E i) T = balancedExcess N E i := by
      intro i
      by_cases hri : i.1 < E % N
      · simp [balancedExcess, hri]
        have hq1 : E / N + 1 ≤ T := by
          have : E / N < T := by simpa [q] using hq
          omega
        simpa using min_eq_left hq1
      · simp [balancedExcess, hri]
        have hbase : E / N ≤ T := by
          exact Nat.le_of_lt (by simpa [q] using hq)
        simpa using min_eq_left hbase
    calc
      (∑ i, min (balancedExcess N E i) T) = ∑ i, balancedExcess N E i := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        simpa using hconst i
      _ = E := balancedExcess_sum N E hN
      _ = min E (N * T) := by
        symm
        apply min_eq_left
        have hq1 : q + 1 ≤ T := by omega
        have hqle : E ≤ N * (q + 1) := by
          have hdecomp : E = N * q + E % N := by
            simpa [q, Nat.add_comm, Nat.mul_comm] using (Nat.mod_add_div E N).symm
          have hmod : E % N ≤ N - 1 := Nat.le_pred_of_lt (Nat.mod_lt _ hN)
          have hle : E ≤ N * q + (N - 1) := by omega
          have hstep : N * q + (N - 1) < N * (q + 1) := by
            calc
              N * q + (N - 1) < N * q + N := by
                exact Nat.add_lt_add_left (Nat.pred_lt (Nat.ne_of_gt hN)) (N * q)
              _ = N * (q + 1) := by
                rw [Nat.mul_add, Nat.mul_one]
          exact le_of_lt (lt_of_le_of_lt hle hstep)
        exact le_trans hqle (Nat.mul_le_mul_left _ hq1)

theorem balancedSpectrum_fixedMass (N M : ℕ) (hN : 0 < N) (hNM : N ≤ M) :
    fixedMassPositiveSpectrum N M (balancedSpectrum N M) := by
  constructor
  · intro i
    unfold balancedSpectrum
    omega
  · have hsumEx : ∑ i, balancedExcess N (M - N) i = M - N := balancedExcess_sum N (M - N) hN
    calc
      ∑ i, balancedSpectrum N M i = ∑ i, (balancedExcess N (M - N) i + 1) := by rfl
      _ = ∑ i, balancedExcess N (M - N) i + ∑ i : Fin N, 1 := by rw [Finset.sum_add_distrib]
      _ = (M - N) + N := by simp [hsumEx]
      _ = M := by omega

private lemma spike_capacity_succ (N E T : ℕ) (hN : 0 < N) :
    foldNatCapacityCurve (spikeSpectrum N (E + N)) (T + 1) = N + min E T := by
  have hpos : ∀ i, 1 ≤ spikeSpectrum N (E + N) i := (spikeSpectrum_fixedMass N (E + N) hN (by omega)).1
  have hcap := capacity_succ_eq_baseline_plus_excess (spikeSpectrum N (E + N)) T hpos
  have hsum :
      ∑ i, min (spikeSpectrum N (E + N) i - 1) T = min E T := by
    let i0 : Fin N := ⟨0, hN⟩
    rw [Finset.sum_eq_single i0]
    · simp [spikeSpectrum, spikeExcess, i0]
    · intro i hi hne
      have hi0 : i.1 ≠ 0 := by
        intro hiz
        apply hne
        apply Fin.ext
        simpa [i0] using hiz
      simp [spikeSpectrum, spikeExcess, hi0]
    · intro hi0
      simp at hi0
  simpa [spikeSpectrum] using hcap.trans (by rw [hsum])

private lemma balanced_capacity_succ (N E T : ℕ) (hN : 0 < N) :
    foldNatCapacityCurve (balancedSpectrum N (E + N)) (T + 1) = N + min E (N * T) := by
  have hpos :
      ∀ i, 1 ≤ balancedSpectrum N (E + N) i :=
    (balancedSpectrum_fixedMass N (E + N) hN (by omega)).1
  have hcap := capacity_succ_eq_baseline_plus_excess (balancedSpectrum N (E + N)) T hpos
  have hsum :
      ∑ i, min (balancedSpectrum N (E + N) i - 1) T = min E (N * T) := by
    simpa [balancedSpectrum] using balancedExcess_capacity N E T hN
  simpa [balancedSpectrum] using hcap.trans (by rw [hsum])

/-- Paper label: `thm:fold-capacity-global-extremizers-fixed-mass`. -/
theorem paper_fold_capacity_global_extremizers_fixed_mass
    (N M : ℕ) (hN : 0 < N) (hNM : N ≤ M) :
    foldCapacityGlobalExtremizersFixedMass N M := by
  intro d hd
  rcases hd with ⟨hpos, hsum⟩
  have hexcess : ∑ i, (d i - 1) = M - N := sum_excess_eq d hpos hsum
  refine ⟨?_, ?_⟩
  · intro T
    cases T with
    | zero =>
        simp [foldNatCapacityCurve]
    | succ S =>
        have hcap := capacity_succ_eq_baseline_plus_excess d S hpos
        have hspike := spike_capacity_succ N (M - N) S hN
        have hmain : N + min (M - N) S ≤ N + ∑ i, min (d i - 1) S :=
          Nat.add_le_add_left (by
            simpa [hexcess] using
              min_sum_le_sum_min (Finset.univ : Finset (Fin N)) (fun i => d i - 1) S) N
        have hspike' : foldNatCapacityCurve (spikeSpectrum N M) (S + 1) = N + min (M - N) S := by
          simpa [Nat.sub_add_cancel hNM] using hspike
        rw [hspike', hcap]
        exact hmain
  · intro T
    cases T with
    | zero =>
        simp [foldNatCapacityCurve]
    | succ S =>
        have hcap := capacity_succ_eq_baseline_plus_excess d S hpos
        have hbal := balanced_capacity_succ N (M - N) S hN
        rw [hcap]
        have hupper1 : (∑ i, Nat.min (d i - 1) S) ≤ M - N := by
          calc
            (∑ i, Nat.min (d i - 1) S) ≤ ∑ i, (d i - 1) := by
              refine Finset.sum_le_sum ?_
              intro i hi
              exact Nat.min_le_left _ _
            _ = M - N := hexcess
        have hupper2 : (∑ i, Nat.min (d i - 1) S) ≤ N * S := sum_min_le_card_mul (fun i => d i - 1) S
        have hmain : N + ∑ i, min (d i - 1) S ≤ N + min (M - N) (N * S) :=
          Nat.add_le_add_left (le_min hupper1 hupper2) N
        have hbal' :
            foldNatCapacityCurve (balancedSpectrum N M) (S + 1) = N + min (M - N) (N * S) := by
          simpa [Nat.sub_add_cancel hNM] using hbal
        rw [hbal']
        exact hmain

end Omega.Folding
