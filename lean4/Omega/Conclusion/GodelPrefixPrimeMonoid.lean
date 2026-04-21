import Mathlib.Tactic

namespace Omega.Conclusion

/-- Prefix-supported exponent lists with strictly positive entries. -/
abbrev PositivePrefix : Type := {xs : List ℕ // ∀ n ∈ xs, 0 < n}

namespace PositivePrefix

/-- The visible prefix length. -/
def length (x : PositivePrefix) : ℕ :=
  x.1.length

/-- The empty prefix plays the role of the unit. -/
def unit : PositivePrefix :=
  ⟨[], by simp⟩

/-- Prefix product induced by concatenation of exponent lists. -/
def odot (x y : PositivePrefix) : PositivePrefix :=
  ⟨x.1 ++ y.1, by
    intro n hn
    rcases List.mem_append.mp hn with hx | hy
    · exact x.2 n hx
    · exact y.2 n hy⟩

/-- A shifted prefix remembers the support offset. -/
abbrev ShiftedPrefix : Type := ℕ × PositivePrefix

/-- Shift a support interval by `k`. -/
def shift (k : ℕ) (x : ShiftedPrefix) : ShiftedPrefix :=
  (x.1 + k, x.2)

/-- Regard a prefix-supported object as based at the origin. -/
def base (x : PositivePrefix) : ShiftedPrefix :=
  (0, x)

/-- Prime-shift by moving the support to the right by `k`. -/
def primeShift (k : ℕ) (x : PositivePrefix) : ShiftedPrefix :=
  shift k (base x)

/-- Support predicate for a shifted prefix. -/
def supportAt (offset : ℕ) (x : PositivePrefix) : ℕ → Prop :=
  fun n => offset ≤ n ∧ n < offset + x.length

/-- Explicit disjointness predicate on supports. -/
def SupportsDisjoint (A B : ℕ → Prop) : Prop :=
  ∀ n, A n → B n → False

/-- Concatenate an encoding and split it again at a chosen cut. -/
def splitEncoding (k : ℕ) (xs : List ℕ) : List ℕ × List ℕ :=
  (xs.take k, xs.drop k)

@[simp] theorem length_unit : unit.length = 0 := rfl

@[simp] theorem length_odot (x y : PositivePrefix) :
    (odot x y).length = x.length + y.length := by
  simp [odot, length]

theorem shift_comp (a b : ℕ) (x : ShiftedPrefix) :
    shift a (shift b x) = shift (a + b) x := by
  cases x
  simp [shift, Nat.add_left_comm, Nat.add_comm]

theorem disjoint_support_multiplication (x y : PositivePrefix) :
    SupportsDisjoint (supportAt 0 x) (supportAt x.length y) := by
  intro n hnLeft hnRight
  dsimp [supportAt] at hnLeft hnRight
  omega

theorem odot_assoc (x y z : PositivePrefix) :
    odot (odot x y) z = odot x (odot y z) := by
  apply Subtype.ext
  simp [odot, List.append_assoc]

@[simp] theorem unit_left (x : PositivePrefix) : odot unit x = x := by
  apply Subtype.ext
  simp [unit, odot]

@[simp] theorem unit_right (x : PositivePrefix) : odot x unit = x := by
  apply Subtype.ext
  simp [unit, odot]

theorem splitEncoding_append (xs ys : List ℕ) :
    splitEncoding xs.length (xs ++ ys) = (xs, ys) := by
  simp [splitEncoding]

end PositivePrefix

open PositivePrefix

/-- Concrete data for the prefix-supported Godel prime monoid package. -/
structure GodelPrefixPrimeMonoidData where
  left : PositivePrefix
  middle : PositivePrefix
  right : PositivePrefix

namespace GodelPrefixPrimeMonoidData

/-- The prefix product closes on prefix-supported codes and the support lengths add. -/
def closedUnderOdot (D : GodelPrefixPrimeMonoidData) : Prop :=
  SupportsDisjoint (supportAt 0 D.left) (supportAt D.left.length D.right) ∧
    (D.left.odot D.right).length = D.left.length + D.right.length

/-- Associativity is witnessed by composing shifts and then concatenating. -/
def associative (D : GodelPrefixPrimeMonoidData) : Prop :=
  shift D.left.length (primeShift D.middle.length D.right) =
      primeShift (D.left.length + D.middle.length) D.right ∧
    (D.left.odot D.middle).odot D.right = D.left.odot (D.middle.odot D.right)

/-- The empty prefix is a two-sided unit. -/
def unitLaw (D : GodelPrefixPrimeMonoidData) : Prop :=
  PositivePrefix.unit.odot D.left = D.left ∧ D.left.odot PositivePrefix.unit = D.left

/-- Splitting the concatenated factorization at the first length recovers the two factors. -/
def concatIso (D : GodelPrefixPrimeMonoidData) : Prop :=
  splitEncoding D.left.length ((D.left.odot D.right).1) = (D.left.1, D.right.1)

theorem closed_under_odot (D : GodelPrefixPrimeMonoidData) : D.closedUnderOdot := by
  exact ⟨disjoint_support_multiplication D.left D.right, length_odot D.left D.right⟩

theorem associative_law (D : GodelPrefixPrimeMonoidData) : D.associative := by
  refine ⟨?_, odot_assoc D.left D.middle D.right⟩
  simpa [PositivePrefix.primeShift, PositivePrefix.base] using
    shift_comp D.left.length D.middle.length (PositivePrefix.base D.right)

theorem unit_law (D : GodelPrefixPrimeMonoidData) : D.unitLaw := by
  exact ⟨unit_left D.left, unit_right D.left⟩

theorem concat_iso (D : GodelPrefixPrimeMonoidData) : D.concatIso := by
  simpa [concatIso] using splitEncoding_append D.left.1 D.right.1

end GodelPrefixPrimeMonoidData

/-- Paper label: `prop:conclusion-godel-prefix-prime-monoid`. -/
theorem paper_conclusion_godel_prefix_prime_monoid (D : GodelPrefixPrimeMonoidData) :
    D.closedUnderOdot ∧ D.associative ∧ D.unitLaw ∧ D.concatIso := by
  exact ⟨D.closed_under_odot, D.associative_law, D.unit_law, D.concat_iso⟩

end Omega.Conclusion
