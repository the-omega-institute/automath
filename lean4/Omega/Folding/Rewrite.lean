import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.Order
import Mathlib.Data.Prod.Lex
import Mathlib.Logic.Relation
import Mathlib.Tactic
import Omega.Folding.InverseLimit

namespace Omega

namespace Rewrite

open Finsupp

/-- Finite-support nonnegative digit configurations for local folding rewrites.
    def:fib-moves -/
abbrev DigitCfg := Nat →₀ Nat

/-- Fibonacci weight carried by the zero-based digit position `k`. -/
def digitWeight (k : Nat) : Nat :=
  Nat.fib (k + 2)

/-- Generic weighted sum over a digit configuration. -/
def weighted (w : Nat → Nat) (a : DigitCfg) : Nat :=
  a.sum (fun k n => n * w k)

/-- The arithmetic value preserved by the rewrite rules. -/
def value : DigitCfg → Nat :=
  weighted digitWeight

/-- Total multiplicity `A(a)` in the paper's termination measure. -/
def mass : DigitCfg → Nat :=
  weighted (fun _ => 1)

/-- First moment `B(a) = \sum (k+1)a_k` in zero-based indexing. -/
def moment : DigitCfg → Nat :=
  weighted (fun k => k + 1)

/-- Critical coordinate `C(a) = a_2`, zero-based as index `1`. -/
def critical (a : DigitCfg) : Nat :=
  a 1

noncomputable def decDigit (a : DigitCfg) (k : Nat) : DigitCfg :=
  a.update k (a k - 1)

noncomputable def incDigit (a : DigitCfg) (k : Nat) : DigitCfg :=
  a + Finsupp.single k 1

@[simp] theorem decDigit_apply_same (a : DigitCfg) (k : Nat) :
    decDigit a k k = a k - 1 := by
  classical
  simp [decDigit]

@[simp] theorem decDigit_apply_ne (a : DigitCfg) {k j : Nat} (h : j ≠ k) :
    decDigit a k j = a j := by
  classical
  simp [decDigit, h]

@[simp] theorem incDigit_apply_same (a : DigitCfg) (k : Nat) :
    incDigit a k k = a k + 1 := by
  classical
  simp [incDigit]

@[simp] theorem incDigit_apply_ne (a : DigitCfg) {k j : Nat} (h : j ≠ k) :
    incDigit a k j = a j := by
  classical
  simp [incDigit, h]

theorem weighted_decDigit_add (w : Nat → Nat) (a : DigitCfg) (k : Nat) (hk : 0 < a k) :
    weighted w (decDigit a k) + w k = weighted w a := by
  classical
  unfold weighted decDigit
  let g : Nat → Nat → Nat := fun j n => n * w j
  have h := Finsupp.sum_update_add a k (a k - 1) g
    (fun _ => by simp [g])
    (fun _ x y => by simp [g, Nat.add_mul])
  have hk' : a k = (a k - 1) + 1 := by
    omega
  rw [hk'] at h
  have h' : (update a k (a k - 1)).sum g + w k + ((a k - 1) * w k) =
      a.sum g + ((a k - 1) * w k) := by
    simpa [g, Nat.add_mul, add_assoc, add_left_comm, add_comm] using h
  exact Nat.add_right_cancel h'

theorem weighted_incDigit (w : Nat → Nat) (a : DigitCfg) (k : Nat) :
    weighted w (incDigit a k) = weighted w a + w k := by
  classical
  unfold weighted incDigit
  rw [Finsupp.sum_add_index']
  · simp [add_comm]
  · intro
    simp
  · intro
    simp [Nat.add_mul]

@[simp] theorem value_decDigit_add (a : DigitCfg) (k : Nat) (hk : 0 < a k) :
    value (decDigit a k) + digitWeight k = value a :=
  weighted_decDigit_add digitWeight a k hk

@[simp] theorem value_incDigit (a : DigitCfg) (k : Nat) :
    value (incDigit a k) = value a + digitWeight k :=
  weighted_incDigit digitWeight a k

@[simp] theorem mass_decDigit_add (a : DigitCfg) (k : Nat) (hk : 0 < a k) :
    mass (decDigit a k) + 1 = mass a := by
  simpa [mass, weighted] using (weighted_decDigit_add (fun _ => 1) a k hk)

@[simp] theorem mass_incDigit (a : DigitCfg) (k : Nat) :
    mass (incDigit a k) = mass a + 1 := by
  simpa [mass, weighted] using (weighted_incDigit (fun _ => 1) a k)

@[simp] theorem moment_decDigit_add (a : DigitCfg) (k : Nat) (hk : 0 < a k) :
    moment (decDigit a k) + (k + 1) = moment a := by
  simpa [moment, weighted] using (weighted_decDigit_add (fun j => j + 1) a k hk)

@[simp] theorem moment_incDigit (a : DigitCfg) (k : Nat) :
    moment (incDigit a k) = moment a + (k + 1) := by
  simpa [moment, weighted] using (weighted_incDigit (fun j => j + 1) a k)

@[simp] theorem digitWeight_zero : digitWeight 0 = 1 := by
  simp [digitWeight]

@[simp] theorem digitWeight_one : digitWeight 1 = 2 := by
  native_decide

@[simp] theorem digitWeight_two : digitWeight 2 = 3 := by
  norm_num [digitWeight]

theorem digitWeight_adj (k : Nat) :
    digitWeight k + digitWeight (k + 1) = digitWeight (k + 2) := by
  calc
    digitWeight k + digitWeight (k + 1) = Nat.fib (k + 2) + Nat.fib (k + 3) := by
      simp [digitWeight]
    _ = Nat.fib ((k + 2) + 1) + Nat.fib (k + 2) := by
      simp [Nat.add_left_comm, Nat.add_comm]
    _ = Nat.fib ((k + 2) + 2) := by
      rw [(fib_succ_succ' (k + 2)).symm]
    _ = digitWeight (k + 2) := by
      simp [digitWeight]

theorem digitWeight_dedupZero :
    2 * digitWeight 0 = digitWeight 1 := by
  norm_num [digitWeight]

theorem digitWeight_dedupOne :
    2 * digitWeight 1 = digitWeight 0 + digitWeight 2 := by
  norm_num [digitWeight]

theorem digitWeight_dedupSucc (k : Nat) :
    digitWeight k + digitWeight (k + 3) = 2 * digitWeight (k + 2) := by
  rw [two_mul]
  calc
    digitWeight k + digitWeight (k + 3)
        = Nat.fib (k + 2) + Nat.fib (k + 5) := by
            simp [digitWeight, Nat.add_left_comm, Nat.add_comm]
    _ = Nat.fib (k + 2) + (Nat.fib (k + 4) + Nat.fib (k + 3)) := by
          rw [fib_succ_succ' (k + 3)]
    _ = (Nat.fib (k + 2) + Nat.fib (k + 3)) + Nat.fib (k + 4) := by
          ac_rfl
    _ = Nat.fib (k + 4) + Nat.fib (k + 4) := by
          have hAdj : Nat.fib (k + 2) + Nat.fib (k + 3) = Nat.fib (k + 4) := by
            calc
              Nat.fib (k + 2) + Nat.fib (k + 3) = Nat.fib ((k + 2) + 1) + Nat.fib (k + 2) := by
                simp [Nat.add_left_comm, Nat.add_comm]
              _ = Nat.fib ((k + 2) + 2) := by
                rw [(fib_succ_succ' (k + 2)).symm]
              _ = Nat.fib (k + 4) := by
                simp [Nat.add_assoc]
          simpa [add_assoc] using congrArg (fun t => t + Nat.fib (k + 4)) hAdj
    _ = digitWeight (k + 2) + digitWeight (k + 2) := by
          simp [digitWeight]

/-- Embed a finite binary word into a digit configuration. -/
noncomputable def iota : {m : Nat} → Word m → DigitCfg
  | 0, _ => 0
  | m + 1, w =>
      let tail := iota (truncate w)
      if Omega.last w then incDigit tail m else tail

@[simp] theorem iota_zero (w : Word 0) : iota w = 0 := rfl

@[simp] theorem iota_snoc (w : Word m) (b : Bool) :
    iota (snoc w b) = if b then incDigit (iota w) m else iota w := by
  simp [iota, truncate_snoc, last_snoc]

@[simp] theorem iota_apply_ge : ∀ {m : Nat} (w : Word m) {k : Nat}, m ≤ k → iota w k = 0
  | 0, _w, _k, _hk => by simp [iota]
  | m + 1, w, k, hk => by
      have hmk : m ≤ k := Nat.le_trans (Nat.le_succ m) hk
      have hne : k ≠ m := by omega
      by_cases hLast : Omega.last w = true
      · simp [iota, hLast, incDigit_apply_ne, hne, iota_apply_ge (truncate w) hmk]
      · simp [iota, hLast, iota_apply_ge (truncate w) hmk]

theorem iota_apply_lt : ∀ {m : Nat} (w : Word m) {k : Nat}, k < m →
    iota w k = if get w k then 1 else 0
  | 0, _w, _k, hk => by
      cases Nat.not_lt_zero _ hk
  | m + 1, w, k, hk => by
      by_cases hkm : k < m
      · have hne : k ≠ m := Nat.ne_of_lt hkm
        by_cases hLast : Omega.last w = true
        · rw [iota, if_pos hLast, incDigit_apply_ne (a := iota (truncate w)) (k := m) (j := k) hne]
          rw [iota_apply_lt (truncate w) hkm, truncate_get_eq (w := w) (i := k) hkm]
        · rw [iota, if_neg hLast, iota_apply_lt (truncate w) hkm, truncate_get_eq (w := w) (i := k) hkm]
      · have hkEq : k = m := Nat.eq_of_lt_succ_of_not_lt hk hkm
        rw [hkEq]
        have hTailZero : iota (truncate w) m = 0 := iota_apply_ge (truncate w) (Nat.le_refl m)
        cases hBit : w ⟨m, Nat.lt_succ_self m⟩ <;> simp [iota, Omega.last, hBit, hTailZero]

theorem iota_pos_iff_get_true {m : Nat} (w : Word m) {k : Nat} :
    0 < iota w k ↔ k < m ∧ get w k = true := by
  constructor
  · intro hk
    by_cases hkm : k < m
    · refine ⟨hkm, ?_⟩
      rw [iota_apply_lt w hkm] at hk
      cases hBit : get w k <;> simp [hBit] at hk ⊢
    · have hge : m ≤ k := Nat.not_lt.mp hkm
      rw [iota_apply_ge w hge] at hk
      omega
  · rintro ⟨hkm, hGet⟩
    rw [iota_apply_lt w hkm, hGet]
    norm_num

@[simp] theorem value_iota : ∀ {m : Nat} (w : Word m), value (iota w) = weight w
  | 0, _w => by
      simp [iota, value, weighted, weight]
  | m + 1, w => by
      by_cases hLast : Omega.last w = true
      · calc
          value (iota w)
              = value (incDigit (iota (truncate w)) m) := by
                  simp [iota, hLast]
          _ = value (iota (truncate w)) + digitWeight m := value_incDigit _ _
          _ = weight (truncate w) + Nat.fib (m + 2) := by
                  rw [value_iota (truncate w), digitWeight]
          _ = weight w := by
                  have hBit : w ⟨m, Nat.lt_succ_self m⟩ = true := by
                    simpa [Omega.last] using hLast
                  simp [weight, hBit]
      · have hLastFalse : Omega.last w = false := by
          cases hBit : Omega.last w <;> simp [hBit] at hLast ⊢
        calc
          value (iota w)
              = value (iota (truncate w)) := by
                  simp [iota, hLastFalse]
          _ = weight (truncate w) := value_iota (truncate w)
          _ = weight w := by
                  have hBit : w ⟨m, Nat.lt_succ_self m⟩ = false := by
                    simpa [Omega.last] using hLastFalse
                  simp [weight, hBit]

/-- Canonical stable prefix read off from a configuration by its Zeckendorf value. -/
def normalPrefix (a : DigitCfg) (m : Nat) : X m :=
  X.ofNat m (value a)

/-- cor:foldm-order-indep-bridge -/
@[simp] theorem normalPrefix_iota_eq_Fold (w : Word m) :
    normalPrefix (iota w) m = Fold w := by
  simp [normalPrefix, Fold, value_iota]

noncomputable def adjTarget (a : DigitCfg) (k : Nat) : DigitCfg :=
  incDigit (decDigit (decDigit a k) (k + 1)) (k + 2)

noncomputable def dedupZeroTarget (a : DigitCfg) : DigitCfg :=
  incDigit (decDigit (decDigit a 0) 0) 1

noncomputable def dedupOneTarget (a : DigitCfg) : DigitCfg :=
  incDigit (incDigit (decDigit (decDigit a 1) 1) 0) 2

noncomputable def dedupSuccTarget (a : DigitCfg) (k : Nat) : DigitCfg :=
  incDigit (incDigit (decDigit (decDigit a (k + 2)) (k + 2)) k) (k + 3)

theorem value_adjTarget (a : DigitCfg) (k : Nat) (hk : 0 < a k) (hk1 : 0 < a (k + 1)) :
    value (adjTarget a k) = value a := by
  have hk1' : 0 < (decDigit a k) (k + 1) := by
    simpa [Nat.succ_ne_self] using hk1
  have h1 := value_decDigit_add a k hk
  have h2 := value_decDigit_add (decDigit a k) (k + 1) hk1'
  have hw := digitWeight_adj k
  calc
    value (adjTarget a k) = value (decDigit (decDigit a k) (k + 1)) + digitWeight (k + 2) := by
      simp [adjTarget]
    _ = value a := by
      omega

theorem value_dedupZeroTarget (a : DigitCfg) (h0 : 1 < a 0) :
    value (dedupZeroTarget a) = value a := by
  have h1 : 0 < (decDigit a 0) 0 := by
    simp [decDigit, h0]
  have hDec1 := value_decDigit_add a 0 (by omega : 0 < a 0)
  have hDec2 := value_decDigit_add (decDigit a 0) 0 h1
  have hw := digitWeight_dedupZero
  calc
    value (dedupZeroTarget a) = value (decDigit (decDigit a 0) 0) + digitWeight 1 := by
      simp [dedupZeroTarget]
    _ = value a := by
      omega

theorem value_dedupOneTarget (a : DigitCfg) (h1 : 1 < a 1) :
    value (dedupOneTarget a) = value a := by
  have h1' : 0 < (decDigit a 1) 1 := by
    simp [decDigit, h1]
  have hDec1 := value_decDigit_add a 1 (by omega : 0 < a 1)
  have hDec2 := value_decDigit_add (decDigit a 1) 1 h1'
  have hw := digitWeight_dedupOne
  calc
    value (dedupOneTarget a)
        = value (decDigit (decDigit a 1) 1) + digitWeight 0 + digitWeight 2 := by
            simp [dedupOneTarget, add_left_comm, add_comm]
    _ = value a := by
      omega

theorem value_dedupSuccTarget (a : DigitCfg) (k : Nat) (hk : 1 < a (k + 2)) :
    value (dedupSuccTarget a k) = value a := by
  have hk' : 0 < (decDigit a (k + 2)) (k + 2) := by
    simp [decDigit, hk]
  have hDec1 := value_decDigit_add a (k + 2) (by omega : 0 < a (k + 2))
  have hDec2 := value_decDigit_add (decDigit a (k + 2)) (k + 2) hk'
  have hw := digitWeight_dedupSucc k
  calc
    value (dedupSuccTarget a k)
        = value (decDigit (decDigit a (k + 2)) (k + 2)) + digitWeight k + digitWeight (k + 3) := by
            simp [dedupSuccTarget, add_left_comm, add_comm]
    _ = value a := by
      omega

theorem mass_adjTarget_add (a : DigitCfg) (k : Nat) (hk : 0 < a k) (hk1 : 0 < a (k + 1)) :
    mass (adjTarget a k) + 1 = mass a := by
  have hk1' : 0 < (decDigit a k) (k + 1) := by
    simpa [Nat.succ_ne_self] using hk1
  have h1 := mass_decDigit_add a k hk
  have h2 := mass_decDigit_add (decDigit a k) (k + 1) hk1'
  have h3 := mass_incDigit (decDigit (decDigit a k) (k + 1)) (k + 2)
  calc
    mass (adjTarget a k) + 1 = mass (decDigit (decDigit a k) (k + 1)) + 2 := by
      simp [adjTarget, h3]
    _ = mass a := by
      omega

theorem mass_dedupZeroTarget_add (a : DigitCfg) (h0 : 1 < a 0) :
    mass (dedupZeroTarget a) + 1 = mass a := by
  have h1 : 0 < (decDigit a 0) 0 := by
    simp [decDigit, h0]
  have hDec1 := mass_decDigit_add a 0 (by omega : 0 < a 0)
  have hDec2 := mass_decDigit_add (decDigit a 0) 0 h1
  have hInc := mass_incDigit (decDigit (decDigit a 0) 0) 1
  calc
    mass (dedupZeroTarget a) + 1 = mass (decDigit (decDigit a 0) 0) + 2 := by
      simp [dedupZeroTarget, hInc]
    _ = mass a := by
      omega

theorem mass_dedupOneTarget (a : DigitCfg) (h1 : 1 < a 1) :
    mass (dedupOneTarget a) = mass a := by
  have h1' : 0 < (decDigit a 1) 1 := by
    simp [decDigit, h1]
  have hDec1 := mass_decDigit_add a 1 (by omega : 0 < a 1)
  have hDec2 := mass_decDigit_add (decDigit a 1) 1 h1'
  have hInc1 := mass_incDigit (decDigit (decDigit a 1) 1) 0
  have hInc2 := mass_incDigit (incDigit (decDigit (decDigit a 1) 1) 0) 2
  calc
    mass (dedupOneTarget a) = mass (decDigit (decDigit a 1) 1) + 2 := by
      simp [dedupOneTarget, hInc1, hInc2]
    _ = mass a := by
      omega

theorem moment_dedupOneTarget (a : DigitCfg) (h1 : 1 < a 1) :
    moment (dedupOneTarget a) = moment a := by
  have h1' : 0 < (decDigit a 1) 1 := by
    simp [decDigit, h1]
  have hDec1 := moment_decDigit_add a 1 (by omega : 0 < a 1)
  have hDec2 := moment_decDigit_add (decDigit a 1) 1 h1'
  have hInc1 := moment_incDigit (decDigit (decDigit a 1) 1) 0
  have hInc2 := moment_incDigit (incDigit (decDigit (decDigit a 1) 1) 0) 2
  calc
    moment (dedupOneTarget a) = moment (decDigit (decDigit a 1) 1) + 4 := by
      simp [dedupOneTarget, hInc1, hInc2]
    _ = moment a := by
      omega

theorem critical_dedupOneTarget_add (a : DigitCfg) (h1 : 1 < a 1) :
    critical (dedupOneTarget a) + 2 = critical a := by
  simp [critical, dedupOneTarget, decDigit, incDigit]
  omega

theorem mass_dedupSuccTarget (a : DigitCfg) (k : Nat) (hk : 1 < a (k + 2)) :
    mass (dedupSuccTarget a k) = mass a := by
  have hk' : 0 < (decDigit a (k + 2)) (k + 2) := by
    simp [decDigit, hk]
  have hDec1 := mass_decDigit_add a (k + 2) (by omega : 0 < a (k + 2))
  have hDec2 := mass_decDigit_add (decDigit a (k + 2)) (k + 2) hk'
  have hInc1 := mass_incDigit (decDigit (decDigit a (k + 2)) (k + 2)) k
  have hInc2 := mass_incDigit (incDigit (decDigit (decDigit a (k + 2)) (k + 2)) k) (k + 3)
  calc
    mass (dedupSuccTarget a k) = mass (decDigit (decDigit a (k + 2)) (k + 2)) + 2 := by
      simp [dedupSuccTarget, hInc1, hInc2]
    _ = mass a := by
      omega

theorem moment_dedupSuccTarget_add (a : DigitCfg) (k : Nat) (hk : 1 < a (k + 2)) :
    moment (dedupSuccTarget a k) + 1 = moment a := by
  have hk' : 0 < (decDigit a (k + 2)) (k + 2) := by
    simp [decDigit, hk]
  have hDec1 := moment_decDigit_add a (k + 2) (by omega : 0 < a (k + 2))
  have hDec2 := moment_decDigit_add (decDigit a (k + 2)) (k + 2) hk'
  have hInc1 := moment_incDigit (decDigit (decDigit a (k + 2)) (k + 2)) k
  have hInc2 := moment_incDigit (incDigit (decDigit (decDigit a (k + 2)) (k + 2)) k) (k + 3)
  calc
    moment (dedupSuccTarget a k) + 1
        = moment (incDigit (decDigit (decDigit a (k + 2)) (k + 2)) k) + (k + 4) + 1 := by
            simp [dedupSuccTarget, hInc2]
    _ = moment (decDigit (decDigit a (k + 2)) (k + 2)) + (k + 1) + (k + 4) + 1 := by
          simp [hInc1]
    _ = moment (decDigit (decDigit a (k + 2)) (k + 2)) + (2 * (k + 3)) := by
          omega
    _ = moment a := by
      omega

/-- One local rewrite step of the folding normalization system. -/
inductive Step : DigitCfg → DigitCfg → Prop
  | adj (a : DigitCfg) (k : Nat) (hk : 0 < a k) (hk1 : 0 < a (k + 1)) :
      Step a (adjTarget a k)
  | dedupZero (a : DigitCfg) (h0 : 1 < a 0) :
      Step a (dedupZeroTarget a)
  | dedupOne (a : DigitCfg) (h1 : 1 < a 1) :
      Step a (dedupOneTarget a)
  | dedupSucc (a : DigitCfg) (k : Nat) (hk : 1 < a (k + 2)) :
      Step a (dedupSuccTarget a k)

/-- prop:fold-rewrite-value-preserving -/
theorem step_value {a b : DigitCfg} (h : Step a b) : value b = value a := by
  cases h with
  | adj k hk hk1 =>
      exact value_adjTarget a k hk hk1
  | dedupZero h0 =>
      exact value_dedupZeroTarget a h0
  | dedupOne h1 =>
      exact value_dedupOneTarget a h1
  | dedupSucc k hk =>
      exact value_dedupSuccTarget a k hk

/-- Each rewrite step does not increase the mass. -/
theorem step_mass_le {a b : DigitCfg} (h : Step a b) : mass b ≤ mass a := by
  cases h with
  | adj k hk hk1 =>
    have := mass_adjTarget_add a k hk hk1; omega
  | dedupZero h0 =>
    have := mass_dedupZeroTarget_add a h0; omega
  | dedupOne h1 =>
    exact le_of_eq (mass_dedupOneTarget a h1)
  | dedupSucc k hk =>
    exact le_of_eq (mass_dedupSuccTarget a k hk)

/-- Lexicographic decrease relation used for termination bookkeeping. -/
def MeasureDrop (a b : DigitCfg) : Prop :=
  mass b < mass a ∨
    (mass b = mass a ∧ moment b < moment a) ∨
    (mass b = mass a ∧ moment b = moment a ∧ critical b < critical a)

/-- The nested lexicographic rank used to prove strong termination. -/
def rankLex (a : DigitCfg) : Nat ×ₗ (Nat ×ₗ Nat) :=
  (toLex (mass a, (toLex (moment a, critical a) : Nat ×ₗ Nat)) : Nat ×ₗ (Nat ×ₗ Nat))

/-- Configurations already in local normal form: binary digits with no adjacent positives. -/
def StableCfg (a : DigitCfg) : Prop :=
  (∀ k : Nat, a k ≤ 1) ∧ ∀ k : Nat, ¬ (0 < a k ∧ 0 < a (k + 1))

/-- A configuration is irreducible when no local rewrite step applies. -/
def Irreducible (a : DigitCfg) : Prop :=
  ∀ ⦃b : DigitCfg⦄, ¬ Step a b

/-- Support bound used to compare finite normal forms inside a fixed window. -/
def SupportedBelow (a : DigitCfg) (m : Nat) : Prop :=
  ∀ k : Nat, m ≤ k → a k = 0

/-- Canonical finite support bound of a digit configuration. -/
def supportBound (a : DigitCfg) : Nat :=
  a.support.sup id + 1

/-- Read a stable binary word off a `{0,1}`-valued configuration supported below `m`. -/
def wordOfStableCfg (a : DigitCfg) (m : Nat) : Word m :=
  fun i => decide (0 < a i.1)

@[simp] theorem get_wordOfStableCfg (a : DigitCfg) {i : Nat} (h : i < m) :
    get (wordOfStableCfg a m) i = decide (0 < a i) := by
  simp [wordOfStableCfg, get, h]

theorem supportedBelow_mono {a : DigitCfg} {m n : Nat}
    (h : SupportedBelow a m) (hmn : m ≤ n) : SupportedBelow a n := by
  intro k hk
  exact h k (le_trans hmn hk)

theorem stableCfg_iota (x : X m) : StableCfg (iota x.1) := by
  refine ⟨?_, ?_⟩
  · intro k
    by_cases hk : k < m
    · rw [iota_apply_lt x.1 hk]
      split <;> omega
    · rw [iota_apply_ge x.1 (Nat.not_lt.mp hk)]
      omega
  · intro k hAdj
    have hk : get x.1 k = true := (iota_pos_iff_get_true x.1).1 hAdj.1 |>.2
    have hk1 : get x.1 (k + 1) = true := (iota_pos_iff_get_true x.1).1 hAdj.2 |>.2
    exact x.2 k hk hk1

theorem supportedBelow_iota (w : Word m) : SupportedBelow (iota w) m := by
  intro k hk
  exact iota_apply_ge w hk

theorem supportedBelow_supportBound (a : DigitCfg) : SupportedBelow a (supportBound a) := by
  intro k hk
  by_contra hk0
  have hMem : k ∈ a.support := by
    exact Finsupp.mem_support_iff.mpr hk0
  have hLe : k ≤ a.support.sup id := by
    exact Finset.le_sup (f := id) hMem
  unfold supportBound at hk
  omega

theorem no11_wordOfStableCfg {a : DigitCfg} (ha : StableCfg a) (m : Nat) :
    No11 (wordOfStableCfg a m) := by
  intro i hi hi1
  have h0 : 0 < a i := by
    have hiLt : i < m := lt_of_get_eq_true hi
    rw [get_wordOfStableCfg a hiLt] at hi
    cases hDec : decide (0 < a i) with
    | false => simp [hDec] at hi
    | true =>
        simpa using hDec
  have h1 : 0 < a (i + 1) := by
    have hi1Lt : i + 1 < m := lt_of_get_eq_true_succ hi1
    rw [get_wordOfStableCfg a hi1Lt] at hi1
    cases hDec : decide (0 < a (i + 1)) with
    | false => simp [hDec] at hi1
    | true =>
        simpa using hDec
  exact (ha.2 i) ⟨h0, h1⟩

theorem iota_wordOfStableCfg_eq {a : DigitCfg} (ha : StableCfg a) (hSup : SupportedBelow a m) :
    iota (wordOfStableCfg a m) = a := by
  ext k
  by_cases hk : k < m
  · rw [iota_apply_lt (wordOfStableCfg a m) hk, get_wordOfStableCfg a hk]
    by_cases hPos : 0 < a k
    · have hLe : a k ≤ 1 := ha.1 k
      have hEq : a k = 1 := by omega
      simp [hEq]
    · have hEq : a k = 0 := by omega
      simp [hEq]
  · have hk' : m ≤ k := Nat.not_lt.mp hk
    rw [iota_apply_ge (wordOfStableCfg a m) hk', hSup k hk']

/-- The stable point represented by a supported `{0,1}` configuration. -/
def stablePoint {a : DigitCfg} (ha : StableCfg a) (m : Nat) : X m :=
  ⟨wordOfStableCfg a m, no11_wordOfStableCfg ha m⟩

@[simp] theorem stablePoint_iota_eq {a : DigitCfg} (ha : StableCfg a) (hSup : SupportedBelow a m) :
    iota (stablePoint ha m).1 = a :=
  iota_wordOfStableCfg_eq ha hSup

theorem irreducible_of_stableCfg {a : DigitCfg} (ha : StableCfg a) : Irreducible a := by
  intro b hStep
  cases hStep with
  | adj k hk hk1 =>
      exact (ha.2 k) ⟨hk, hk1⟩
  | dedupZero h0 =>
      exact Nat.not_lt_of_ge (ha.1 0) h0
  | dedupOne h1 =>
      exact Nat.not_lt_of_ge (ha.1 1) h1
  | dedupSucc k hk =>
      exact Nat.not_lt_of_ge (ha.1 (k + 2)) hk

theorem stableCfg_of_irreducible {a : DigitCfg} (ha : Irreducible a) : StableCfg a := by
  refine ⟨?_, ?_⟩
  · intro k
    cases k with
    | zero =>
        by_contra hk
        have hk' : 1 < a 0 := Nat.lt_of_not_ge hk
        exact ha (Step.dedupZero a hk')
    | succ k =>
        cases k with
        | zero =>
            by_contra hk
            have hk' : 1 < a 1 := Nat.lt_of_not_ge hk
            exact ha (Step.dedupOne a hk')
        | succ k =>
            by_contra hk
            have hk' : 1 < a (k + 2) := Nat.lt_of_not_ge hk
            exact ha (Step.dedupSucc a k hk')
  · intro k hAdj
    exact ha (Step.adj a k hAdj.1 hAdj.2)

theorem irreducible_iff_stableCfg {a : DigitCfg} : Irreducible a ↔ StableCfg a := by
  constructor
  · exact stableCfg_of_irreducible
  · exact irreducible_of_stableCfg

theorem step_measureDrop {a b : DigitCfg} (h : Step a b) : MeasureDrop a b := by
  cases h with
  | adj k hk hk1 =>
      left
      have hMass := mass_adjTarget_add a k hk hk1
      omega
  | dedupZero h0 =>
      left
      have hMass := mass_dedupZeroTarget_add a h0
      omega
  | dedupOne h1 =>
      right
      right
      have hMass := mass_dedupOneTarget a h1
      have hMoment := moment_dedupOneTarget a h1
      have hCrit := critical_dedupOneTarget_add a h1
      refine ⟨?_, ?_, ?_⟩ <;> omega
  | dedupSucc k hk =>
      right
      left
      have hMass := mass_dedupSuccTarget a k hk
      have hMoment := moment_dedupSuccTarget_add a k hk
      refine ⟨?_, ?_⟩ <;> omega

theorem step_rankLex {a b : DigitCfg} (h : Step a b) : rankLex b < rankLex a := by
  rcases step_measureDrop h with hMass | hRest
  · change
      toLex (mass b, (toLex (moment b, critical b) : Nat ×ₗ Nat)) <
        toLex (mass a, (toLex (moment a, critical a) : Nat ×ₗ Nat))
    rw [Prod.Lex.toLex_lt_toLex]
    exact Or.inl hMass
  · change
      toLex (mass b, (toLex (moment b, critical b) : Nat ×ₗ Nat)) <
        toLex (mass a, (toLex (moment a, critical a) : Nat ×ₗ Nat))
    rw [Prod.Lex.toLex_lt_toLex]
    refine Or.inr ?_
    rcases hRest with ⟨hMassEq, hMomentLt⟩ | ⟨hMassEq, hMomentEq, hCritLt⟩
    · refine ⟨hMassEq, ?_⟩
      change
        toLex (moment b, critical b) < toLex (moment a, critical a)
      rw [Prod.Lex.toLex_lt_toLex]
      exact Or.inl hMomentLt
    · refine ⟨hMassEq, ?_⟩
      change
        toLex (moment b, critical b) < toLex (moment a, critical a)
      rw [Prod.Lex.toLex_lt_toLex]
      exact Or.inr ⟨hMomentEq, hCritLt⟩

theorem step_wellFounded : WellFounded (flip Step) :=
  WellFounded.mono (InvImage.wf rankLex wellFounded_lt) (fun _ _ h => step_rankLex h)

/-- The local rewrite relation is strongly terminating.
    thm:fold-rewrite-strong-termination -/
theorem step_stronglyTerminating : WellFounded (flip Step) :=
  step_wellFounded

@[simp] theorem normalPrefix_step {a b : DigitCfg} (h : Step a b) :
    normalPrefix b m = normalPrefix a m := by
  simp [normalPrefix, step_value h]

theorem irreducible_iota_of_stable (x : X m) : Irreducible (iota x.1) :=
  irreducible_of_stableCfg (stableCfg_iota x)

theorem irreducible_iota_normalPrefix (a : DigitCfg) (m : Nat) :
    Irreducible (iota (normalPrefix a m).1) :=
  irreducible_iota_of_stable (normalPrefix a m)

@[simp] theorem irreducible_iota_Fold (w : Word m) : Irreducible (iota (Fold w).1) :=
  irreducible_iota_of_stable (Fold w)

/-- thm:fold-rewrite-supported-normal-form -/
theorem irreducible_supported_eq_iota_normalPrefix {a : DigitCfg}
    (hIrr : Irreducible a) (hSup : SupportedBelow a m) :
    a = iota (normalPrefix a m).1 := by
  let x : X m := stablePoint ((irreducible_iff_stableCfg).1 hIrr) m
  have hIota : iota x.1 = a := stablePoint_iota_eq ((irreducible_iff_stableCfg).1 hIrr) hSup
  have hNorm : normalPrefix a m = x := by
    calc
      normalPrefix a m = normalPrefix (iota x.1) m := by simp [hIota]
      _ = Fold x.1 := normalPrefix_iota_eq_Fold x.1
      _ = x := Fold_stable x
  calc
    a = iota x.1 := hIota.symm
    _ = iota (normalPrefix a m).1 := by rw [hNorm]

/-- cor:fold-rewrite-irred-unique-on-window -/
theorem irreducible_eq_of_normalPrefix_eq {a b : DigitCfg}
    (hIrrA : Irreducible a) (hIrrB : Irreducible b)
    (hSupA : SupportedBelow a m) (hSupB : SupportedBelow b m)
    (hNorm : normalPrefix a m = normalPrefix b m) :
    a = b := by
  rw [irreducible_supported_eq_iota_normalPrefix hIrrA hSupA,
    irreducible_supported_eq_iota_normalPrefix hIrrB hSupB]
  simp [hNorm]

/-- thm:fold-rewrite-rtrans-preserves-normalprefix -/
theorem reflTransGen_normalPrefix {a b : DigitCfg} (h : Relation.ReflTransGen Step a b) :
    normalPrefix b m = normalPrefix a m := by
  induction h with
  | refl =>
      rfl
  | tail hab hStep ih =>
      simpa [normalPrefix_step hStep] using ih

theorem irreducible_reflTransGen_eq_iota_normalPrefix {a b : DigitCfg}
    (hab : Relation.ReflTransGen Step a b)
    (hIrr : Irreducible b) (hSup : SupportedBelow b m) :
    b = iota (normalPrefix a m).1 := by
  calc
    b = iota (normalPrefix b m).1 :=
      irreducible_supported_eq_iota_normalPrefix hIrr hSup
    _ = iota (normalPrefix a m).1 := by
      rw [reflTransGen_normalPrefix hab]

/-- thm:fold-rewrite-terminal-irred-unique -/
theorem irreducible_terminal_unique {a b c : DigitCfg}
    (hab : Relation.ReflTransGen Step a b) (hac : Relation.ReflTransGen Step a c)
    (hIrrB : Irreducible b) (hIrrC : Irreducible c)
    (hSupB : SupportedBelow b m) (hSupC : SupportedBelow c m) :
    b = c := by
  rw [irreducible_reflTransGen_eq_iota_normalPrefix hab hIrrB hSupB,
    irreducible_reflTransGen_eq_iota_normalPrefix hac hIrrC hSupC]

/-- cor:fold-rewrite-terminal-equals-fold -/
theorem irreducible_terminal_eq_fold {w : Word m} {b : DigitCfg}
    (hab : Relation.ReflTransGen Step (iota w) b)
    (hIrr : Irreducible b) (hSup : SupportedBelow b m) :
    b = iota (Fold w).1 := by
  calc
    b = iota (normalPrefix (iota w) m).1 :=
      irreducible_reflTransGen_eq_iota_normalPrefix hab hIrr hSup
    _ = iota (Fold w).1 := by
      rw [normalPrefix_iota_eq_Fold]

/-- Mass is non-increasing along rewrite chains. -/
theorem reflTransGen_mass_le {a b : DigitCfg} (h : Relation.ReflTransGen Step a b) :
    mass b ≤ mass a := by
  induction h with
  | refl => exact le_refl _
  | tail hab hStep ih => exact le_trans (step_mass_le hStep) ih

theorem reflTransGen_value {a b : DigitCfg} (h : Relation.ReflTransGen Step a b) :
    value b = value a := by
  induction h with
  | refl =>
      rfl
  | tail hab hStep ih =>
      simpa [step_value hStep] using ih

theorem irreducible_eq_of_value_eq {a b : DigitCfg}
    (hIrrA : Irreducible a) (hIrrB : Irreducible b) (hVal : value a = value b) :
    a = b := by
  let m := max (supportBound a) (supportBound b)
  have hSupA : SupportedBelow a m :=
    supportedBelow_mono (supportedBelow_supportBound a) (Nat.le_max_left _ _)
  have hSupB : SupportedBelow b m :=
    supportedBelow_mono (supportedBelow_supportBound b) (Nat.le_max_right _ _)
  have hNorm : normalPrefix a m = normalPrefix b m := by
    simp [normalPrefix, hVal]
  exact irreducible_eq_of_normalPrefix_eq hIrrA hIrrB hSupA hSupB hNorm

/-- thm:fold-rewrite-terminal-irred-unique-unbounded -/
theorem irreducible_terminal_unique_unbounded {a b c : DigitCfg}
    (hab : Relation.ReflTransGen Step a b) (hac : Relation.ReflTransGen Step a c)
    (hIrrB : Irreducible b) (hIrrC : Irreducible c) :
    b = c := by
  apply irreducible_eq_of_value_eq hIrrB hIrrC
  calc
    value b = value a := reflTransGen_value hab
    _ = value c := (reflTransGen_value hac).symm

/-- thm:fold-rewrite-terminal-exists -/
theorem exists_irreducible_descendant (a : DigitCfg) :
    ∃ b, Relation.ReflTransGen Step a b ∧ Irreducible b := by
  let S : Set DigitCfg := {b | Relation.ReflTransGen Step a b}
  have hne : S.Nonempty := ⟨a, Relation.ReflTransGen.refl⟩
  obtain ⟨b, hbS, hmin⟩ := step_wellFounded.has_min S hne
  refine ⟨b, hbS, ?_⟩
  intro c hStep
  have hcS : S c := Relation.ReflTransGen.tail hbS hStep
  exact hmin c hcS hStep

/-- thm:fold-rewrite-confluent -/
theorem step_confluent {a b c : DigitCfg}
    (hab : Relation.ReflTransGen Step a b) (hac : Relation.ReflTransGen Step a c) :
    Relation.Join (Relation.ReflTransGen Step) b c := by
  obtain ⟨nb, hbn, hIrrB⟩ := exists_irreducible_descendant b
  obtain ⟨nc, hcn, hIrrC⟩ := exists_irreducible_descendant c
  have habn : Relation.ReflTransGen Step a nb := Relation.ReflTransGen.trans hab hbn
  have hacn : Relation.ReflTransGen Step a nc := Relation.ReflTransGen.trans hac hcn
  have hEq : nb = nc := irreducible_terminal_unique_unbounded habn hacn hIrrB hIrrC
  refine ⟨nb, hbn, ?_⟩
  simpa [hEq] using hcn

/-- thm:fold-rewrite-locally-confluent -/
theorem step_locallyConfluent {a b c : DigitCfg} (hab : Step a b) (hac : Step a c) :
    Relation.Join (Relation.ReflTransGen Step) b c :=
  step_confluent (Relation.ReflTransGen.single hab) (Relation.ReflTransGen.single hac)

-- ══════════════════════════════════════════════════════════════
-- Phase 233: Weight rigidity
-- ══════════════════════════════════════════════════════════════

/-- Weight rigidity: w(k+2)=w(k+1)+w(k) with w(0)=1,w(1)=2 forces w=digitWeight.
    lem:fold-local-weight-rigidity-fibonacci -/
theorem weight_rigidity_fibonacci (w : Nat → Nat)
    (hadj : ∀ k, w k + w (k + 1) = w (k + 2))
    (hw0 : w 0 = 1) (hw1 : w 1 = 2) :
    ∀ k, w k = digitWeight k := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    match k with
    | 0 => rw [hw0, digitWeight_zero]
    | 1 => rw [hw1, digitWeight_one]
    | k + 2 =>
      have hadj' := hadj k
      have h1 := ih k (by omega)
      have h2 := ih (k + 1) (by omega)
      have h3 := digitWeight_adj k
      omega

/-- Value is invariant under all rewrite rules. prop:val-invariant -/
theorem value_invariant_step (a b : DigitCfg) (h : Step a b) : value a = value b :=
  (step_value h).symm

-- ══════════════════════════════════════════════════════════════
-- Phase 241
-- ══════════════════════════════════════════════════════════════

/-- The adjacency rewrite e_{k+1}+e_{k+2} → e_{k+3} preserves Val.
    Equivalently: F(k+2) + F(k+3) = F(k+4) for all k.
    prop:orbits-preserve-val -/
theorem paper_orbits_preserve_val (k : Nat) :
    Nat.fib (k + 2) + Nat.fib (k + 3) = Nat.fib (k + 4) := by
  have := Nat.fib_add_two (n := k + 2)
  rw [show k + 2 + 2 = k + 4 from by omega, show k + 2 + 1 = k + 3 from by omega] at this
  omega

end Rewrite

end Omega
