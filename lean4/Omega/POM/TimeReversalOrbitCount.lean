import Mathlib.Tactic
import Omega.Core.Fib
import Omega.POM.ToggleOrder

namespace Omega.POM

open Omega.POM.ToggleOrder

private lemma pom_time_reversal_orbit_count_component_parity (ℓ : ℕ) :
    Nat.fib (ℓ + 2) % 2 = timeReversalFix ℓ % 2 := by
  by_cases hEven : ℓ % 2 = 0
  · rw [timeReversalFix, if_pos hEven, Omega.fib_mod_two_period (ℓ + 2),
      Omega.fib_mod_two_period (ℓ / 2 + 1)]
    have hk : (ℓ / 2) % 3 = 0 ∨ (ℓ / 2) % 3 = 1 ∨ (ℓ / 2) % 3 = 2 := by
      omega
    rcases hk with hk | hk | hk
    · have h1 : (ℓ + 2) % 3 = 2 := by omega
      have h2 : (ℓ / 2 + 1) % 3 = 1 := by omega
      rw [h1, h2]
      native_decide
    · have h1 : (ℓ + 2) % 3 = 1 := by omega
      have h2 : (ℓ / 2 + 1) % 3 = 2 := by omega
      rw [h1, h2]
      native_decide
    · have h1 : (ℓ + 2) % 3 = 0 := by omega
      have h2 : (ℓ / 2 + 1) % 3 = 0 := by omega
      simp [h1, h2]
  · rw [timeReversalFix, if_neg hEven, Omega.fib_mod_two_period (ℓ + 2),
      Omega.fib_mod_two_period (ℓ / 2 + 3)]
    have hk : (ℓ / 2) % 3 = 0 ∨ (ℓ / 2) % 3 = 1 ∨ (ℓ / 2) % 3 = 2 := by
      omega
    rcases hk with hk | hk | hk
    · have h1 : (ℓ + 2) % 3 = 0 := by omega
      have h2 : (ℓ / 2 + 3) % 3 = 0 := by omega
      simp [h1, h2]
    · have h1 : (ℓ + 2) % 3 = 2 := by omega
      have h2 : (ℓ / 2 + 3) % 3 = 1 := by omega
      rw [h1, h2]
      native_decide
    · have h1 : (ℓ + 2) % 3 = 1 := by omega
      have h2 : (ℓ / 2 + 3) % 3 = 2 := by omega
      rw [h1, h2]
      native_decide

private lemma pom_time_reversal_orbit_count_fix_le_vertex : ∀ lengths : List Nat,
    fiberTimeReversalFixCount lengths ≤ fiberTimeReversalVertexCount lengths
  | [] => by
      simp [fiberTimeReversalFixCount, fiberTimeReversalVertexCount]
  | ℓ :: lengths => by
      have hhead : timeReversalFix ℓ ≤ Nat.fib (ℓ + 2) := by
        cases ℓ with
        | zero =>
            native_decide
        | succ n =>
            exact timeReversalFix_le_total (Nat.succ n) (Nat.succ_le_succ (Nat.zero_le n))
      have htail := pom_time_reversal_orbit_count_fix_le_vertex lengths
      simpa [fiberTimeReversalFixCount, fiberTimeReversalVertexCount] using
        Nat.mul_le_mul hhead htail

private lemma pom_time_reversal_orbit_count_parity : ∀ lengths : List Nat,
    fiberTimeReversalVertexCount lengths % 2 = fiberTimeReversalFixCount lengths % 2
  | [] => by
      simp [fiberTimeReversalVertexCount, fiberTimeReversalFixCount]
  | ℓ :: lengths => by
      calc
        fiberTimeReversalVertexCount (ℓ :: lengths) % 2 =
            (Nat.fib (ℓ + 2) % 2) * (fiberTimeReversalVertexCount lengths % 2) % 2 := by
              simp [fiberTimeReversalVertexCount, Nat.mul_mod]
        _ = (timeReversalFix ℓ % 2) * (fiberTimeReversalFixCount lengths % 2) % 2 := by
              rw [pom_time_reversal_orbit_count_component_parity,
                pom_time_reversal_orbit_count_parity]
        _ = fiberTimeReversalFixCount (ℓ :: lengths) % 2 := by
              simp [fiberTimeReversalFixCount, Nat.mul_mod]

/-- Paper label: `cor:pom-time-reversal-orbit-count`. The orbit count of the fiberwise
time-reversal involution is the fixed-point count plus the transposition count, equivalently the
half-sum of the total state count and the fixed-point count. -/
theorem paper_pom_time_reversal_orbit_count (lengths : List Nat) :
    fiberTimeReversalFixCount lengths + fiberTimeReversalSignExp lengths =
      (fiberTimeReversalVertexCount lengths + fiberTimeReversalFixCount lengths) / 2 := by
  unfold fiberTimeReversalSignExp
  have hle := pom_time_reversal_orbit_count_fix_le_vertex lengths
  have hpar := pom_time_reversal_orbit_count_parity lengths
  omega

private lemma pom_time_reversal_fixedpoints_extremes_fix_pos (ℓ : Nat) (hℓ : 1 ≤ ℓ) :
    0 < timeReversalFix ℓ := by
  unfold timeReversalFix
  split
  · exact Nat.fib_pos.mpr (by omega)
  · exact Nat.fib_pos.mpr (by omega)

private lemma pom_time_reversal_fixedpoints_extremes_fix_eq_total_iff
    (ℓ : Nat) (hℓ : 1 ≤ ℓ) :
    timeReversalFix ℓ = Nat.fib (ℓ + 2) ↔ ℓ = 1 := by
  constructor
  · intro h
    by_cases hℓ1 : ℓ = 1
    · exact hℓ1
    exfalso
    by_cases hEven : ℓ % 2 = 0
    · have hidx : 2 ≤ ℓ / 2 + 1 := by omega
      have hidx_lt : ℓ / 2 + 1 < ℓ + 2 := by omega
      have hlt : Nat.fib (ℓ / 2 + 1) < Nat.fib (ℓ + 2) :=
        (Nat.fib_lt_fib hidx).2 hidx_lt
      have hfix : timeReversalFix ℓ = Nat.fib (ℓ / 2 + 1) := by
        simp [timeReversalFix, hEven]
      omega
    · have hidx : 2 ≤ ℓ / 2 + 3 := by omega
      have hidx_lt : ℓ / 2 + 3 < ℓ + 2 := by omega
      have hlt : Nat.fib (ℓ / 2 + 3) < Nat.fib (ℓ + 2) :=
        (Nat.fib_lt_fib hidx).2 hidx_lt
      have hfix : timeReversalFix ℓ = Nat.fib (ℓ / 2 + 3) := by
        simp [timeReversalFix, hEven]
      omega
  · intro h
    subst h
    simp [timeReversalFix]

private lemma pom_time_reversal_fixedpoints_extremes_fix_eq_one_iff
    (ℓ : Nat) (hℓ : 1 ≤ ℓ) :
    timeReversalFix ℓ = 1 ↔ ℓ = 2 := by
  constructor
  · intro h
    by_cases hℓ2 : ℓ = 2
    · exact hℓ2
    exfalso
    by_cases hEven : ℓ % 2 = 0
    · have hge4 : 4 ≤ ℓ := by omega
      have hidx : 2 < ℓ / 2 + 1 := by omega
      have hlt : Nat.fib 2 < Nat.fib (ℓ / 2 + 1) :=
        (Nat.fib_lt_fib (by omega : 2 ≤ 2)).2 hidx
      have hfix : timeReversalFix ℓ = Nat.fib (ℓ / 2 + 1) := by
        simp [timeReversalFix, hEven]
      have hgt : 1 < timeReversalFix ℓ := by
        rw [hfix]
        simpa using hlt
      omega
    · have hidx : 2 < ℓ / 2 + 3 := by omega
      have hlt : Nat.fib 2 < Nat.fib (ℓ / 2 + 3) :=
        (Nat.fib_lt_fib (by omega : 2 ≤ 2)).2 hidx
      have hfix : timeReversalFix ℓ = Nat.fib (ℓ / 2 + 3) := by
        simp [timeReversalFix, hEven]
      have hgt : 1 < timeReversalFix ℓ := by
        rw [hfix]
        simpa using hlt
      omega
  · intro h
    subst h
    simp [timeReversalFix]

private lemma pom_time_reversal_fixedpoints_extremes_fix_count_pos :
    ∀ lengths : List Nat, (∀ ℓ ∈ lengths, 1 ≤ ℓ) → 0 < fiberTimeReversalFixCount lengths
  | [], _ => by simp [fiberTimeReversalFixCount]
  | ℓ :: lengths, hpos => by
      have hhead : 0 < timeReversalFix ℓ :=
        pom_time_reversal_fixedpoints_extremes_fix_pos ℓ (hpos ℓ (by simp))
      have htail : 0 < fiberTimeReversalFixCount lengths :=
        pom_time_reversal_fixedpoints_extremes_fix_count_pos lengths (by
          intro m hm
          exact hpos m (by simp [hm]))
      simpa [fiberTimeReversalFixCount] using Nat.mul_pos hhead htail

private lemma pom_time_reversal_fixedpoints_extremes_vertex_count_pos
    (lengths : List Nat) : 0 < fiberTimeReversalVertexCount lengths := by
  induction lengths with
  | nil =>
      simp [fiberTimeReversalVertexCount]
  | cons ℓ lengths ih =>
      have hfib : 0 < Nat.fib (ℓ + 2) := Nat.fib_pos.mpr (by omega)
      change 0 < Nat.fib (ℓ + 2) * fiberTimeReversalVertexCount lengths
      exact Nat.mul_pos hfib ih

private lemma pom_time_reversal_fixedpoints_extremes_mul_eq_of_le
    {a b c d : Nat} (hab : a ≤ b) (hcd : c ≤ d) (hc : 0 < c) (hb : 0 < b)
    (h : a * c = b * d) :
    a = b ∧ c = d := by
  constructor
  · by_contra hne
    have hlt : a < b := lt_of_le_of_ne hab hne
    have hprod : a * c < b * d :=
      lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hlt hc) (Nat.mul_le_mul_left b hcd)
    omega
  · by_contra hne
    have hlt : c < d := lt_of_le_of_ne hcd hne
    have hprod : a * c < b * d :=
      lt_of_le_of_lt (Nat.mul_le_mul_right c hab) (Nat.mul_lt_mul_of_pos_left hlt hb)
    omega

private lemma pom_time_reversal_fixedpoints_extremes_eq_vertex_iff :
    ∀ lengths : List Nat, (∀ ℓ ∈ lengths, 1 ≤ ℓ) →
      (fiberTimeReversalFixCount lengths = fiberTimeReversalVertexCount lengths ↔
        ∀ ℓ ∈ lengths, ℓ = 1)
  | [], _ => by
      simp [fiberTimeReversalFixCount, fiberTimeReversalVertexCount]
  | head :: lengths, hpos => by
      have hhead_pos : 1 ≤ head := hpos head (by simp)
      have htail_pos : ∀ m ∈ lengths, 1 ≤ m := by
        intro m hm
        exact hpos m (by simp [hm])
      have htail :=
        pom_time_reversal_fixedpoints_extremes_eq_vertex_iff lengths htail_pos
      constructor
      · intro h
        have hhead_le : timeReversalFix head ≤ Nat.fib (head + 2) :=
          timeReversalFix_le_total head hhead_pos
        have htail_le : fiberTimeReversalFixCount lengths ≤ fiberTimeReversalVertexCount lengths :=
          pom_time_reversal_orbit_count_fix_le_vertex lengths
        have htail_fix_pos : 0 < fiberTimeReversalFixCount lengths :=
          pom_time_reversal_fixedpoints_extremes_fix_count_pos lengths htail_pos
        have hhead_vertex_pos : 0 < Nat.fib (head + 2) := Nat.fib_pos.mpr (by omega)
        have hsplit :=
          pom_time_reversal_fixedpoints_extremes_mul_eq_of_le hhead_le htail_le
            htail_fix_pos hhead_vertex_pos (by
              simpa [fiberTimeReversalFixCount, fiberTimeReversalVertexCount] using h)
        intro m hm
        simp only [List.mem_cons] at hm
        rcases hm with hm | hm
        · exact hm.trans
            ((pom_time_reversal_fixedpoints_extremes_fix_eq_total_iff head hhead_pos).1
              hsplit.1)
        · exact htail.1 hsplit.2 m hm
      · intro hall
        have hhead : timeReversalFix head = Nat.fib (head + 2) := by
          exact (pom_time_reversal_fixedpoints_extremes_fix_eq_total_iff head hhead_pos).2
            (hall head (by simp))
        have htail_eq : fiberTimeReversalFixCount lengths = fiberTimeReversalVertexCount lengths :=
          htail.2 (by
            intro m hm
            exact hall m (by simp [hm]))
        rw [fiberTimeReversalFixCount, fiberTimeReversalVertexCount, hhead, htail_eq]

private lemma pom_time_reversal_fixedpoints_extremes_eq_one_iff :
    ∀ lengths : List Nat, (∀ ℓ ∈ lengths, 1 ≤ ℓ) →
      (fiberTimeReversalFixCount lengths = 1 ↔ ∀ ℓ ∈ lengths, ℓ = 2)
  | [], _ => by
      simp [fiberTimeReversalFixCount]
  | head :: lengths, hpos => by
      have hhead_pos : 1 ≤ head := hpos head (by simp)
      have htail_pos : ∀ m ∈ lengths, 1 ≤ m := by
        intro m hm
        exact hpos m (by simp [hm])
      have htail :=
        pom_time_reversal_fixedpoints_extremes_eq_one_iff lengths htail_pos
      constructor
      · intro h
        have hsplit :
            timeReversalFix head = 1 ∧ fiberTimeReversalFixCount lengths = 1 := by
          simpa [fiberTimeReversalFixCount] using h
        have hhead_one : timeReversalFix head = 1 := hsplit.1
        have htail_one : fiberTimeReversalFixCount lengths = 1 := hsplit.2
        intro m hm
        simp only [List.mem_cons] at hm
        rcases hm with hm | hm
        · exact hm.trans
            ((pom_time_reversal_fixedpoints_extremes_fix_eq_one_iff head hhead_pos).1 hhead_one)
        · exact htail.1 htail_one m hm
      · intro hall
        have hhead : timeReversalFix head = 1 := by
          exact (pom_time_reversal_fixedpoints_extremes_fix_eq_one_iff head hhead_pos).2
            (hall head (by simp))
        have htail_eq : fiberTimeReversalFixCount lengths = 1 :=
          htail.2 (by
            intro m hm
            exact hall m (by simp [hm]))
        rw [fiberTimeReversalFixCount, hhead, htail_eq]

/-- Paper label: `prop:pom-time-reversal-fixedpoints-extremes`. For positive path lengths,
the fiberwise time-reversal fixed count reaches the total fiber size exactly for all singleton
paths, and it is one exactly for all two-vertex paths. -/
theorem paper_pom_time_reversal_fixedpoints_extremes (lengths : List ℕ)
    (hpos : ∀ ℓ ∈ lengths, 1 ≤ ℓ) :
    ((fiberTimeReversalFixCount lengths = fiberTimeReversalVertexCount lengths ↔
      ∀ ℓ ∈ lengths, ℓ = 1) ∧
      (fiberTimeReversalFixCount lengths = 1 ↔ ∀ ℓ ∈ lengths, ℓ = 2)) := by
  exact ⟨pom_time_reversal_fixedpoints_extremes_eq_vertex_iff lengths hpos,
    pom_time_reversal_fixedpoints_extremes_eq_one_iff lengths hpos⟩

end Omega.POM
