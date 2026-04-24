import Mathlib.Data.Finsupp.Weight
import Mathlib.Tactic
import Omega.GroupUnification.GroupJGPrimeRegisterInitialObject

namespace Omega.Conclusion

open Omega.GroupUnification

/-- The prime-shift semidirect ledger `𝒫 ⋊ ℕ` encoded by finitely supported exponent vectors
together with the shift counter. -/
abbrev PrimeShiftLedger := PrimeRegisterObject × ℕ

/-- Semidirect multiplication `(r,k) · (s,ℓ) = (r + Σ^k s, k + ℓ)`. -/
noncomputable def primeShiftMul (x y : PrimeShiftLedger) : PrimeShiftLedger :=
  (x.1 + ((primeRegisterShift^[x.2]) y.1), x.2 + y.2)

/-- The total multiplicity `Ω(r) = ∑_t r_t`. -/
def primeShiftOmega (r : PrimeRegisterObject) : ℕ :=
  r.sum fun _ n => n

/-- The visible two-coordinate quotient `(r,k) ↦ (k, Ω(r))`. -/
def primeShiftPi (x : PrimeShiftLedger) : ℕ × ℕ :=
  (x.2, primeShiftOmega x.1)

/-- Additivity on the visible quotient `ℕ²`. -/
def NatPairAdditive {A : Type*} [Add A] (g : ℕ × ℕ → A) : Prop :=
  ∀ u v, g (u.1 + v.1, u.2 + v.2) = g u + g v

/-- The factor map determined by the two visible generators. -/
def primeShiftFactor {A : Type*} [AddMonoid A] (a ζ : A) : ℕ × ℕ → A
  | (k, m) => k • a + m • ζ

/-- The visible part on the prime-register side is the total multiplicity times the common basis
value. -/
def primeShiftVisiblePart {A : Type*} [AddMonoid A] (ζ : A) (r : PrimeRegisterObject) : A :=
  primeShiftOmega r • ζ

theorem primeShiftOmega_add (r s : PrimeRegisterObject) :
    primeShiftOmega (r + s) = primeShiftOmega r + primeShiftOmega s := by
  unfold primeShiftOmega
  rw [Finsupp.sum_add_index']
  · intro a
    simp
  · intro a b c
    simp

@[simp] theorem primeShiftOmega_zero : primeShiftOmega (0 : PrimeRegisterObject) = 0 := by
  simp [primeShiftOmega]

@[simp] theorem primeShiftOmega_single (t n : ℕ) :
    primeShiftOmega (Finsupp.single t n) = n := by
  simp [primeShiftOmega]

theorem primeShiftFactor_additive {A : Type*} [AddCommMonoid A] (a ζ : A) :
    NatPairAdditive (primeShiftFactor a ζ) := by
  intro u v
  rcases u with ⟨k, m⟩
  rcases v with ⟨ℓ, n⟩
  simp [primeShiftFactor, add_nsmul, add_assoc, add_left_comm]

private theorem natPairAdditive_zero {A : Type*} [AddCommGroup A] {g : ℕ × ℕ → A}
    (hg : NatPairAdditive g) : g (0, 0) = 0 := by
  have h : g (0, 0) = g (0, 0) + g (0, 0) := by simpa using hg (0, 0) (0, 0)
  have h' := congrArg (fun x => x - g (0, 0)) h
  simpa using h'.symm

private theorem natPairAdditive_first {A : Type*} [AddCommGroup A] {g : ℕ × ℕ → A}
    (hg : NatPairAdditive g) : ∀ k : ℕ, g (k, 0) = k • g (1, 0)
  | 0 => by simpa using natPairAdditive_zero hg
  | k + 1 => by
      have h := hg (k, 0) (1, 0)
      simpa [natPairAdditive_first hg k, Nat.succ_eq_add_one, add_nsmul, one_nsmul, add_assoc,
        add_left_comm, add_comm] using h

private theorem natPairAdditive_second {A : Type*} [AddCommGroup A] {g : ℕ × ℕ → A}
    (hg : NatPairAdditive g) : ∀ m : ℕ, g (0, m) = m • g (0, 1)
  | 0 => by simpa using natPairAdditive_zero hg
  | m + 1 => by
      have h := hg (0, m) (0, 1)
      simpa [natPairAdditive_second hg m, Nat.succ_eq_add_one, add_nsmul, one_nsmul, add_assoc,
        add_left_comm, add_comm] using h

private theorem natPairAdditive_eq_factor {A : Type*} [AddCommGroup A] {g : ℕ × ℕ → A}
    (hg : NatPairAdditive g) (u : ℕ × ℕ) :
    g u = primeShiftFactor (g (1, 0)) (g (0, 1)) u := by
  rcases u with ⟨k, m⟩
  have h := hg (k, 0) (0, m)
  simpa [primeShiftFactor, natPairAdditive_first hg k, natPairAdditive_second hg m, add_assoc,
    add_left_comm, add_comm] using h

private theorem natPairAdditive_unique {A : Type*} [AddCommGroup A] {g h : ℕ × ℕ → A}
    (hg : NatPairAdditive g) (hh : NatPairAdditive h) (h10 : g (1, 0) = h (1, 0))
    (h01 : g (0, 1) = h (0, 1)) : g = h := by
  funext u
  rw [natPairAdditive_eq_factor hg u, natPairAdditive_eq_factor hh u, h10, h01]

/-- Paper label: `thm:conclusion-prime-shift-phase-visible-two-generator`. -/
theorem paper_conclusion_prime_shift_phase_visible_two_generator {A : Type*} [AddCommGroup A]
    (f : PrimeShiftLedger → A) (hzero : f (0, 0) = 0)
    (hmul : ∀ x y, f (primeShiftMul x y) = f x + f y) :
    ∃! g : ℕ × ℕ → A,
      NatPairAdditive g ∧ ∀ x : PrimeShiftLedger, f x = g (primeShiftPi x) := by
  let a : A := f (0, 1)
  let ζ : A := f (primeBasis 0, 0)
  let fRegister : PrimeRegisterObject →+ A :=
    { toFun := fun r => f (r, 0)
      map_zero' := hzero
      map_add' := by
        intro r s
        simpa [primeShiftMul] using hmul (r, 0) (s, 0) }
  have hshift : ∀ r : PrimeRegisterObject, fRegister (primeRegisterShift r) = fRegister r := by
    intro r
    have hleft := hmul (0, 1) (r, 0)
    have hright := hmul (primeRegisterShift r, 0) (0, 1)
    have hleft' : f (primeRegisterShift r, 1) = a + fRegister r := by
      simpa [a, fRegister, primeShiftMul, add_assoc, add_left_comm, add_comm] using hleft
    have hright' : f (primeRegisterShift r, 1) = fRegister (primeRegisterShift r) + a := by
      simpa [a, fRegister, primeShiftMul, add_assoc, add_left_comm, add_comm] using hright
    have hEq : fRegister r + a = fRegister (primeRegisterShift r) + a := by
      calc
        fRegister r + a = a + fRegister r := by simp [add_comm]
        _ = f (primeRegisterShift r, 1) := by simpa using hleft'.symm
        _ = fRegister (primeRegisterShift r) + a := hright'
    have hEq' : a + fRegister r = a + fRegister (primeRegisterShift r) := by
      simpa [add_comm] using hEq
    have hCancel := congrArg (fun x => x - a) hEq'
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hCancel.symm
  have hbasis : ∀ t : ℕ, fRegister (primeBasis t) = ζ := by
    intro t
    induction t with
    | zero =>
        rfl
    | succ t ih =>
        calc
          fRegister (primeBasis (t + 1))
              = fRegister (primeRegisterShift (primeBasis t)) := by
                  rw [primeRegisterShift_basis]
          _ = fRegister (primeBasis t) := hshift (primeBasis t)
          _ = ζ := ih
  have hsingle : ∀ t n : ℕ, fRegister (Finsupp.single t n) = n • ζ := by
    intro t n
    calc
      fRegister (Finsupp.single t n) = n • fRegister (primeBasis t) := by
        rw [show Finsupp.single t n = n • primeBasis t by simp [primeBasis]]
        exact map_nsmul fRegister _ _
      _ = n • ζ := by rw [hbasis t]
  let gRegister : PrimeRegisterObject →+ A :=
    { toFun := primeShiftVisiblePart ζ
      map_zero' := by simp [primeShiftVisiblePart]
      map_add' := by
        intro r s
        simp [primeShiftVisiblePart, primeShiftOmega_add, add_nsmul] }
  have hRegisterEq : fRegister = gRegister := by
    apply Finsupp.addHom_ext
    intro t n
    simp [gRegister, primeShiftVisiblePart, hsingle t n]
  have hRegister : ∀ r : PrimeRegisterObject, f (r, 0) = primeShiftVisiblePart ζ r := by
    intro r
    change fRegister r = gRegister r
    rw [hRegisterEq]
  have hStep : ∀ k : ℕ, f (0, k) = k • a := by
    intro k
    induction k with
    | zero =>
        simpa [a] using hzero
    | succ k ih =>
        have h := hmul (0, k) (0, 1)
        simpa [a, primeShiftMul, ih, Nat.succ_eq_add_one, add_nsmul, one_nsmul, add_assoc,
          add_left_comm, add_comm] using h
  have hFactor : ∀ x : PrimeShiftLedger, f x = primeShiftFactor a ζ (primeShiftPi x) := by
    rintro ⟨r, k⟩
    have h := hmul (r, 0) (0, k)
    simpa [a, ζ, primeShiftMul, primeShiftPi, primeShiftFactor, primeShiftVisiblePart, hRegister r,
      hStep k, add_assoc, add_left_comm, add_comm] using h
  refine ⟨primeShiftFactor a ζ, ?_, ?_⟩
  · refine ⟨primeShiftFactor_additive a ζ, hFactor⟩
  · intro g hg
    rcases hg with ⟨hgAdd, hgFactor⟩
    have h10 : g (1, 0) = primeShiftFactor a ζ (1, 0) := by
      simpa [a, primeShiftPi, primeShiftOmega, primeShiftFactor] using (hgFactor (0, 1)).symm
    have h01 : g (0, 1) = primeShiftFactor a ζ (0, 1) := by
      simpa [ζ, primeShiftPi, primeBasis, primeShiftOmega, primeShiftFactor] using
        (hgFactor (primeBasis 0, 0)).symm
    exact natPairAdditive_unique hgAdd (primeShiftFactor_additive a ζ) h10 h01

end Omega.Conclusion
