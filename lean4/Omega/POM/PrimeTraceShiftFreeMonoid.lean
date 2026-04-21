import Mathlib.Data.List.Basic
import Mathlib.Tactic

namespace Omega.POM

/-- The finite prime-register trace model used in the paper-facing wrapper. -/
abbrev PrimeTraceRegister := List ℕ

/-- The length of a finite prime-register trace. -/
def primeTraceLength (r : PrimeTraceRegister) : ℕ :=
  r.length

/-- Shifted trace multiplication is realized by concatenation, since the right trace is appended
after all occupied coordinates of the left trace. -/
def primeTraceMul (r s : PrimeTraceRegister) : PrimeTraceRegister :=
  r ++ s

/-- The trace image of an event word is obtained by recording the event codes in order. -/
def primeTraceWord {E : Type*} (code : E → ℕ) (w : List E) : PrimeTraceRegister :=
  w.map code

/-- The trace image of the event-word monoid. -/
abbrev PrimeTraceImage {E : Type*} (code : E → ℕ) :=
  {r : PrimeTraceRegister // ∃ w : List E, primeTraceWord code w = r}

/-- The trace map into its image. -/
def primeTraceToImage {E : Type*} (code : E → ℕ) (w : List E) : PrimeTraceImage code :=
  ⟨primeTraceWord code w, ⟨w, rfl⟩⟩

/-- The unit trace. -/
def primeTraceImageOne {E : Type*} (code : E → ℕ) : PrimeTraceImage code :=
  primeTraceToImage code []

/-- Concatenating a pair of event words concatenates their trace images. -/
lemma primeTraceWord_append {E : Type*} (code : E → ℕ) (u v : List E) :
    primeTraceWord code (u ++ v) = primeTraceMul (primeTraceWord code u) (primeTraceWord code v) := by
  simp [primeTraceWord, primeTraceMul, List.map_append]

/-- Multiplication on the trace image, induced by concatenation of event words. -/
noncomputable def primeTraceImageMul {E : Type*} (code : E → ℕ)
    (x y : PrimeTraceImage code) : PrimeTraceImage code := by
  refine ⟨primeTraceMul x.1 y.1, ?_⟩
  rcases x.2 with ⟨u, hu⟩
  rcases y.2 with ⟨v, hv⟩
  refine ⟨u ++ v, ?_⟩
  simp [primeTraceWord_append, primeTraceMul, hu, hv]

lemma primeTraceMul_assoc (r s t : PrimeTraceRegister) :
    primeTraceMul (primeTraceMul r s) t = primeTraceMul r (primeTraceMul s t) := by
  simp [primeTraceMul, List.append_assoc]

lemma primeTraceLength_mul (r s : PrimeTraceRegister) :
    primeTraceLength (primeTraceMul r s) = primeTraceLength r + primeTraceLength s := by
  simp [primeTraceLength, primeTraceMul]

lemma primeTraceWord_injective {E : Type*} {code : E → ℕ} (hcode : Function.Injective code) :
    Function.Injective (primeTraceWord code) := by
  intro u
  induction u with
  | nil =>
      intro v huv
      cases v with
      | nil =>
          rfl
      | cons b v =>
          cases huv
  | cons a u ihu =>
      intro v huv
      cases v with
      | nil =>
          cases huv
      | cons b v =>
          simp [primeTraceWord] at huv
          rcases huv with ⟨hab, huv⟩
          have hab' : a = b := hcode hab
          subst hab'
          have huv' : u = v := ihu huv
          subst huv'
          rfl

/-- Paper-facing statement for the shifted-addition prime-register trace model.  The trace image is
closed under shifted multiplication, lengths add, and the trace map from event words to its image
is bijective and multiplicative. -/
def pomPrimeTraceShiftFreeMonoidStatement : Prop :=
  ∀ {E : Type*} (code : E → ℕ),
    Function.Injective code →
    (∀ e : E, 0 < code e) →
      (∀ r s t : PrimeTraceRegister,
        primeTraceMul (primeTraceMul r s) t = primeTraceMul r (primeTraceMul s t)) ∧
      (∀ r s : PrimeTraceRegister,
        primeTraceLength (primeTraceMul r s) = primeTraceLength r + primeTraceLength s) ∧
      primeTraceToImage code [] = primeTraceImageOne code ∧
      Function.Bijective (primeTraceToImage code) ∧
      (∀ u v : List E,
        primeTraceToImage code (u ++ v) =
          primeTraceImageMul code (primeTraceToImage code u) (primeTraceToImage code v))

theorem paper_pom_prime_trace_shift_free_monoid : pomPrimeTraceShiftFreeMonoidStatement := by
  intro E code hcode _hpos
  refine ⟨primeTraceMul_assoc, primeTraceLength_mul, rfl, ?_, ?_⟩
  · constructor
    · intro u v huv
      exact primeTraceWord_injective hcode (Subtype.mk.inj huv)
    · intro x
      rcases x.2 with ⟨w, hw⟩
      refine ⟨w, ?_⟩
      apply Subtype.ext
      simpa [primeTraceToImage] using hw
  · intro u v
    apply Subtype.ext
    simp [primeTraceImageMul, primeTraceToImage, primeTraceWord_append, primeTraceMul]

end Omega.POM
