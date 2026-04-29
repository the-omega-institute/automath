import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete data for the halting-ledger fiber profile.

The optional halting time is `none` for the non-halting case and `some N` for a finite
halting time.  The stored fiber-cardinality and log-volume ledgers are required to match
the active-prefix formula; the first-difference kink is then derived from `min`. -/
structure conclusion_halting_ledger_defect_kink_data where
  haltingTime : Option ℕ
  fiberCardinality : ℕ → ℕ
  logVolumeUnits : ℕ → ℕ
  fiberCardinality_activePrefix :
    ∀ m,
      fiberCardinality m =
        2 ^
          match haltingTime with
          | none => m
          | some N => min m N
  logVolume_activePrefix :
    ∀ m,
      logVolumeUnits m =
        match haltingTime with
        | none => m
        | some N => min m N

namespace conclusion_halting_ledger_defect_kink_data

/-- The number of free bits left by the resolution-`m` projection. -/
def freeBits (D : conclusion_halting_ledger_defect_kink_data) (m : ℕ) : ℕ :=
  match D.haltingTime with
  | none => m
  | some N => min m N

/-- Uniform cardinality of every visible fiber at resolution `m`. -/
def uniform_fiber_cardinality (D : conclusion_halting_ledger_defect_kink_data) : Prop :=
  ∀ m, D.fiberCardinality m = 2 ^ D.freeBits m

/-- Closed form for the logarithmic fiber-volume defect, measured in units of `log 2`. -/
def kappa_closed_form (D : conclusion_halting_ledger_defect_kink_data) : Prop :=
  ∀ m, D.logVolumeUnits m = D.freeBits m

/-- First difference of the closed-form ledger profile. -/
def firstDifference (D : conclusion_halting_ledger_defect_kink_data) (m : ℕ) : ℕ :=
  D.freeBits (m + 1) - D.freeBits m

/-- The expected slope profile: constant one before the finite halting time and zero after. -/
def expectedSlope (D : conclusion_halting_ledger_defect_kink_data) (m : ℕ) : ℕ :=
  match D.haltingTime with
  | none => 1
  | some N => if m < N then 1 else 0

/-- The kink formula for the first difference of the ledger profile. -/
def slope_kink_formula (D : conclusion_halting_ledger_defect_kink_data) : Prop :=
  ∀ m, D.firstDifference m = D.expectedSlope m

end conclusion_halting_ledger_defect_kink_data

open conclusion_halting_ledger_defect_kink_data

lemma conclusion_halting_ledger_defect_kink_min_succ_sub_min
    (m N : ℕ) : min (m + 1) N - min m N = if m < N then 1 else 0 := by
  by_cases h : m < N
  · have hMin : min m N = m := Nat.min_eq_left (Nat.le_of_lt h)
    have hSuccMin : min (m + 1) N = m + 1 := Nat.min_eq_left (Nat.succ_le_of_lt h)
    rw [hMin, hSuccMin]
    simp [h]
  · have hNle : N ≤ m := Nat.le_of_not_gt h
    have hMin : min m N = N := Nat.min_eq_right hNle
    have hSuccMin : min (m + 1) N = N := Nat.min_eq_right (Nat.le_trans hNle (Nat.le_succ m))
    simp [h, hMin, hSuccMin]

/-- Paper label: `prop:conclusion-halting-ledger-defect-kink`. -/
theorem paper_conclusion_halting_ledger_defect_kink
    (D : conclusion_halting_ledger_defect_kink_data) :
    D.uniform_fiber_cardinality ∧ D.kappa_closed_form ∧ D.slope_kink_formula := by
  constructor
  · intro m
    cases h : D.haltingTime with
    | none =>
        simpa [conclusion_halting_ledger_defect_kink_data.freeBits, h] using
          D.fiberCardinality_activePrefix m
    | some N =>
        simpa [conclusion_halting_ledger_defect_kink_data.freeBits, h] using
          D.fiberCardinality_activePrefix m
  constructor
  · intro m
    cases h : D.haltingTime with
    | none =>
        simpa [conclusion_halting_ledger_defect_kink_data.freeBits, h] using
          D.logVolume_activePrefix m
    | some N =>
        simpa [conclusion_halting_ledger_defect_kink_data.freeBits, h] using
          D.logVolume_activePrefix m
  · intro m
    cases h : D.haltingTime with
    | none =>
        simp [
          conclusion_halting_ledger_defect_kink_data.firstDifference,
          conclusion_halting_ledger_defect_kink_data.freeBits,
          conclusion_halting_ledger_defect_kink_data.expectedSlope, h]
    | some N =>
        simpa [
          conclusion_halting_ledger_defect_kink_data.firstDifference,
          conclusion_halting_ledger_defect_kink_data.freeBits,
          conclusion_halting_ledger_defect_kink_data.expectedSlope, h]
          using conclusion_halting_ledger_defect_kink_min_succ_sub_min m N

end Omega.Conclusion
