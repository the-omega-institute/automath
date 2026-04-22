import Mathlib.Tactic
import Omega.Conclusion.CanonicalSliceExactFixedpointCount

namespace Omega.Conclusion

/-- Infinite digit sequences on the canonical slice alphabet `{0, …, M}`. -/
abbrev CanonicalDigitStream (D : CanonicalSliceData) := ℕ → Fin (D.M + 1)

/-- The length-`k` prefix of a digit stream, viewed as a canonical layer block. -/
def canonicalPrefix (D : CanonicalSliceData) (k : ℕ) (a : CanonicalDigitStream D) :
    D.fixedPointsAtLayer k :=
  fun i => a i

/-- The left shift on digit streams. -/
def canonicalStrip (D : CanonicalSliceData) (a : CanonicalDigitStream D) : CanonicalDigitStream D :=
  fun n => a (n + 1)

/-- The canonical coded fixed-point model, identified with the underlying digit stream. -/
abbrev CanonicalFixedpointCode (D : CanonicalSliceData) := CanonicalDigitStream D

/-- The digit encoder from streams to the coded fixed-point model. -/
def canonicalDigitEncoder (D : CanonicalSliceData) (a : CanonicalDigitStream D) :
    CanonicalFixedpointCode D :=
  a

/-- The decoder is the identity on the coded fixed-point model. -/
def canonicalDigitDecoder (D : CanonicalSliceData) (c : CanonicalFixedpointCode D) :
    CanonicalDigitStream D :=
  c

/-- The shift transported to the coded fixed-point side. -/
def canonicalCodeShift (D : CanonicalSliceData) (c : CanonicalFixedpointCode D) :
    CanonicalFixedpointCode D :=
  canonicalStrip D c

/-- Two canonical streams are equal once all of their finite prefixes agree. -/
lemma canonicalPrefix_unique (D : CanonicalSliceData) {a b : CanonicalDigitStream D}
    (hprefix : ∀ k : ℕ, canonicalPrefix D k a = canonicalPrefix D k b) : a = b := by
  funext n
  have h := congrFun (hprefix (n + 1)) ⟨n, Nat.lt_succ_self n⟩
  simpa [canonicalPrefix] using h

/-- Every canonical prefix determines a unique fixed point in its layer. -/
lemma canonicalPrefix_fixedpoint_unique (D : CanonicalSliceData) (a : CanonicalDigitStream D)
    (k : ℕ) :
    ∃! x, D.IsFixedPoint (canonicalPrefix D k a) k x := by
  exact (paper_conclusion_canonical_slice_exact_fixedpoint_count D k).1
    (canonicalPrefix D k a) (by simp [CanonicalSliceData.layer])

/-- The encoder/decoder equivalence between canonical streams and their fixed-point codes. -/
def canonicalDigitEquiv (D : CanonicalSliceData) :
    CanonicalDigitStream D ≃ CanonicalFixedpointCode D where
  toFun := canonicalDigitEncoder D
  invFun := canonicalDigitDecoder D
  left_inv := by
    intro a
    rfl
  right_inv := by
    intro c
    rfl

/-- Paper-facing stream-level conjugacy statement for the canonical fixed-point model: finite
prefixes determine unique fixed points, they separate streams, and the digit encoder conjugates
the left shift with the strip map on coded fixed points. -/
def CanonicalFixedpointFullshiftConjugacyStatement (D : CanonicalSliceData) : Prop :=
  (∀ a : CanonicalDigitStream D, ∀ k : ℕ, ∃! x, D.IsFixedPoint (canonicalPrefix D k a) k x) ∧
    (∀ a b : CanonicalDigitStream D,
      (∀ k : ℕ, canonicalPrefix D k a = canonicalPrefix D k b) → a = b) ∧
    Function.Bijective (canonicalDigitEncoder D) ∧
    Function.LeftInverse (canonicalDigitDecoder D) (canonicalDigitEncoder D) ∧
    Function.RightInverse (canonicalDigitDecoder D) (canonicalDigitEncoder D) ∧
    ∀ a : CanonicalDigitStream D,
      canonicalDigitEncoder D (canonicalStrip D a) =
        canonicalCodeShift D (canonicalDigitEncoder D a)

/-- Paper label: `thm:conclusion-canonical-fixedpoint-fullshift-conjugacy`. The canonical slice
block model yields unique finite prefixes, these prefixes separate streams, and the stream
encoding is a strict conjugacy between the one-sided full shift and the strip map on the coded
fixed-point model. -/
theorem paper_conclusion_canonical_fixedpoint_fullshift_conjugacy (D : CanonicalSliceData) :
    CanonicalFixedpointFullshiftConjugacyStatement D := by
  refine ⟨?_, ?_, (canonicalDigitEquiv D).bijective, (canonicalDigitEquiv D).left_inv,
    (canonicalDigitEquiv D).right_inv, ?_⟩
  · intro a k
    exact canonicalPrefix_fixedpoint_unique D a k
  · intro a b hab
    exact canonicalPrefix_unique D hab
  · intro a
    rfl

end Omega.Conclusion
