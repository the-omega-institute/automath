import Mathlib.Data.Finsupp.Ext
import Mathlib.Data.Finsupp.Weight
import Mathlib.Tactic

namespace Omega.GroupUnification

/-- A Gödel-shift encoder is an additive commutative monoid with a shift endomorphism and a
distinguished seed element. -/
structure GShiftEncoder where
  Carrier : Type
  instAddCommMonoid : AddCommMonoid Carrier
  shift : Carrier →+ Carrier
  seed : Carrier

attribute [instance] GShiftEncoder.instAddCommMonoid

/-- The concrete prime-register object: finitely supported exponent vectors indexed by prime
coordinates. We index the prime coordinates by `ℕ`, with index `0` standing for the first prime. -/
abbrev PrimeRegisterObject := ℕ →₀ ℕ

/-- The basis vector supported on the `t`-th prime coordinate. -/
noncomputable def primeBasis (t : ℕ) : PrimeRegisterObject :=
  Finsupp.single t 1

/-- The shift sends the `t`-th prime basis vector to the next basis vector. -/
noncomputable def primeRegisterShift : PrimeRegisterObject →+ PrimeRegisterObject :=
  Finsupp.weight fun t => primeBasis (t + 1)

/-- The orbit of the distinguished seed under repeated shifts. -/
def shiftedSeed (E : GShiftEncoder) : ℕ → E.Carrier
  | 0 => E.seed
  | t + 1 => E.shift (shiftedSeed E t)

/-- The additive extension that sends the `t`-th prime basis vector to the `t`-fold shift of the
distinguished seed. -/
noncomputable def primeRegisterLift (E : GShiftEncoder) : PrimeRegisterObject →+ E.Carrier :=
  Finsupp.weight (shiftedSeed E)

/-- The concrete encoder of finitely supported sequences into the prime-register object. -/
noncomputable def primeRegisterSequenceEncoder : PrimeRegisterObject →+ PrimeRegisterObject :=
  Finsupp.weight primeBasis

/-- The prime-register object is initial for `E` if there is a unique additive morphism carrying
the distinguished basis vector to `E.seed` and intertwining the shifts. -/
def PrimeRegisterInitialFor (E : GShiftEncoder) : Prop :=
  ∃! φ : PrimeRegisterObject →+ E.Carrier,
    φ (primeBasis 0) = E.seed ∧
      ∀ x : PrimeRegisterObject, φ (primeRegisterShift x) = E.shift (φ x)

@[simp] theorem primeRegisterShift_single (t n : ℕ) :
    primeRegisterShift (Finsupp.single t n) = n • primeBasis (t + 1) := by
  simpa [primeRegisterShift] using
    (Finsupp.weight_single (w := fun s => primeBasis (s + 1)) t n)

@[simp] theorem primeRegisterShift_basis (t : ℕ) :
    primeRegisterShift (primeBasis t) = primeBasis (t + 1) := by
  simp [primeBasis]

@[simp] theorem primeRegisterLift_single (E : GShiftEncoder) (t n : ℕ) :
    primeRegisterLift E (Finsupp.single t n) = n • shiftedSeed E t := by
  simpa [primeRegisterLift] using (Finsupp.weight_single (w := shiftedSeed E) t n)

@[simp] theorem primeRegisterLift_basis (E : GShiftEncoder) (t : ℕ) :
    primeRegisterLift E (primeBasis t) = shiftedSeed E t := by
  simp [primeBasis]

@[simp] theorem primeRegisterSequenceEncoder_apply (x : PrimeRegisterObject) :
    primeRegisterSequenceEncoder x = x := by
  apply Finsupp.ext
  intro t
  simp [primeRegisterSequenceEncoder, Finsupp.weight_apply, primeBasis]

theorem primeRegisterSequenceEncoder_injective :
    Function.Injective primeRegisterSequenceEncoder := by
  intro x y hxy
  simpa [primeRegisterSequenceEncoder_apply] using hxy

private theorem primeRegisterLift_commutes (E : GShiftEncoder) :
    AddMonoidHom.comp (primeRegisterLift E) primeRegisterShift =
      AddMonoidHom.comp E.shift (primeRegisterLift E) := by
  apply Finsupp.addHom_ext
  intro t n
  simp [shiftedSeed]

private theorem eq_primeRegisterLift_of_compatible
    (E : GShiftEncoder) (φ : PrimeRegisterObject →+ E.Carrier)
    (hseed : φ (primeBasis 0) = E.seed)
    (hshift : ∀ x : PrimeRegisterObject, φ (primeRegisterShift x) = E.shift (φ x)) :
    φ = primeRegisterLift E := by
  have hbasis : ∀ t : ℕ, φ (primeBasis t) = shiftedSeed E t := by
    intro t
    induction t with
    | zero =>
        simpa [primeBasis, shiftedSeed] using hseed
    | succ t ih =>
        calc
          φ (primeBasis (t + 1)) = φ (primeRegisterShift (primeBasis t)) := by
            rw [primeRegisterShift_basis]
          _ = E.shift (φ (primeBasis t)) := hshift (primeBasis t)
          _ = E.shift (shiftedSeed E t) := by rw [ih]
          _ = shiftedSeed E (t + 1) := rfl
  apply Finsupp.addHom_ext
  intro t n
  calc
    φ (Finsupp.single t n) = φ (n • primeBasis t) := by
      simp [primeBasis]
    _ = n • φ (primeBasis t) := by
      simp
    _ = n • shiftedSeed E t := by
      rw [hbasis t]
    _ = primeRegisterLift E (Finsupp.single t n) := by
      symm
      exact primeRegisterLift_single E t n

/-- The prime-register object is the initial Gödel-shift encoder.
    thm:group-jg-prime-register-initial-object -/
theorem paper_group_jg_prime_register_initial_object (E : GShiftEncoder) :
    PrimeRegisterInitialFor E := by
  refine ⟨primeRegisterLift E, ?_, ?_⟩
  · constructor
    · simp [primeBasis, shiftedSeed]
    · intro x
      change (AddMonoidHom.comp (primeRegisterLift E) primeRegisterShift) x =
        (AddMonoidHom.comp E.shift (primeRegisterLift E)) x
      rw [primeRegisterLift_commutes]
  · intro φ hφ
    exact eq_primeRegisterLift_of_compatible E φ hφ.1 hφ.2

end Omega.GroupUnification
