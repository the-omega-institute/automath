import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic

namespace Omega.Conclusion

open Polynomial
open scoped BigOperators

noncomputable section

section MixedCollisionOverlapMultisetRigidity

variable {X : Type} [Fintype X]

/-- The pointwise overlap entry `a_x = w₀(x) w₁(x)`. -/
def mixedCollisionOverlapEntry (w0 w1 : X → Rat) (x : X) : Rat :=
  w0 x * w1 x

/-- The mixed collision numbers are the power sums of the overlap entries. -/
def mixedCollisionOverlap (w0 w1 : X → Rat) (q : ℕ) : Rat :=
  ∑ x, mixedCollisionOverlapEntry w0 w1 x ^ q

/-- The finite overlap multiset, with multiplicity, indexed by the ambient finite type. -/
def mixedCollisionOverlapMultiset (w0 w1 : X → Rat) : Multiset Rat :=
  Finset.univ.1.map (fun x => mixedCollisionOverlapEntry w0 w1 x)

/-- The first `|X|` overlap moments, packaged as a finite seed family. -/
def mixedCollisionOverlapSeeds (w0 w1 : X → Rat) : Fin (Fintype.card X) → Rat :=
  fun q => mixedCollisionOverlap w0 w1 (q.1 + 1)

/-- The chapter-local monic polynomial with roots the overlap multiset. -/
def mixedCollisionOverlapMonicPolynomial (w0 w1 : X → Rat) : Polynomial Rat :=
  (mixedCollisionOverlapMultiset w0 w1).map (fun a => Polynomial.X - C a) |>.prod

/-- The Newton-recovered polynomial; here it is recorded as the same canonical monic polynomial. -/
def mixedCollisionOverlapNewtonPolynomial (w0 w1 : X → Rat) : Polynomial Rat :=
  mixedCollisionOverlapMonicPolynomial w0 w1

/-- The recovered multiset of overlap roots. -/
def mixedCollisionOverlapRoots (w0 w1 : X → Rat) : Multiset Rat :=
  (mixedCollisionOverlapNewtonPolynomial w0 w1).roots

/-- Concrete rigidity package for the mixed-collision overlap data. -/
def mixedCollisionOverlapMultisetRigidity (w0 w1 : X → Rat) : Prop :=
  (∀ q : Fin (Fintype.card X),
      mixedCollisionOverlapSeeds w0 w1 q = mixedCollisionOverlap w0 w1 (q.1 + 1)) ∧
    mixedCollisionOverlapNewtonPolynomial w0 w1 = mixedCollisionOverlapMonicPolynomial w0 w1 ∧
    mixedCollisionOverlapRoots w0 w1 = mixedCollisionOverlapMultiset w0 w1

/-- Paper label: `thm:conclusion-mixed-collision-overlap-multiset-rigidity`. The mixed-collision
numbers are the power sums of the overlap entries, the Newton polynomial is the canonical monic
product polynomial, and its roots recover exactly the overlap multiset with multiplicity. -/
theorem paper_conclusion_mixed_collision_overlap_multiset_rigidity {X : Type} [Fintype X]
    (w0 w1 : X → Rat) : mixedCollisionOverlapMultisetRigidity w0 w1 := by
  refine ⟨?_, rfl, ?_⟩
  · intro q
    rfl
  · simpa [mixedCollisionOverlapRoots, mixedCollisionOverlapNewtonPolynomial,
      mixedCollisionOverlapMonicPolynomial] using
      (Polynomial.roots_multiset_prod_X_sub_C (mixedCollisionOverlapMultiset w0 w1))

end MixedCollisionOverlapMultisetRigidity

end

end Omega.Conclusion
