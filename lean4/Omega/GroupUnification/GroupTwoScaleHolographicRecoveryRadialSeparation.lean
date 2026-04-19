import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace Omega.GroupUnification

/-- Toy polynomial model recorded by its finite root set. -/
structure RadialPolynomial where
  roots : Finset ℤ

/-- The scaled reciprocal cofactor root set appearing in the pullback factorization. -/
def pveeRoots (P : RadialPolynomial) (r : ℤ) : Finset ℤ :=
  P.roots.image fun z => (r ^ 2) * z

/-- The pullback factorization `F_r = P * Pvee(r^2 z)` on root sets. -/
def pullbackFactorization (P : RadialPolynomial) (r : ℤ) : Finset ℤ :=
  P.roots ∪ pveeRoots P r

/-- Toy gcd on root sets, modeled by intersection. -/
def gcdRootSet (A B : Finset ℤ) : Finset ℤ :=
  A ∩ B

/-- Radial separation keeps the two cofactor root sets disjoint from `P` and from each other. -/
def radiallySeparated (P : RadialPolynomial) (r1 r2 : ℤ) : Prop :=
  Disjoint P.roots (pveeRoots P r1) ∧
    Disjoint P.roots (pveeRoots P r2) ∧
    Disjoint (pveeRoots P r1) (pveeRoots P r2)

/-- Recovery holds when the gcd of the two pullbacks recovers exactly the original root set. -/
def recoverableByGcd (P : RadialPolynomial) (r1 r2 : ℤ) : Prop :=
  gcdRootSet (pullbackFactorization P r1) (pullbackFactorization P r2) = P.roots

/-- Under radial separation, the common roots of the two pullback factors are exactly the
original roots of `P`, so normalizing the gcd recovers `P`.
    thm:group-two-scale-holographic-recovery-radial-separation -/
theorem paper_group_two_scale_holographic_recovery_radial_separation
    {P : RadialPolynomial} {r1 r2 : ℤ} :
    radiallySeparated P r1 r2 -> recoverableByGcd P r1 r2 := by
  intro hsep
  rcases hsep with ⟨hP1, hP2, h12⟩
  ext x
  simp [gcdRootSet, pullbackFactorization]
  constructor
  · intro hx
    rcases hx with ⟨hx1, hx2⟩
    rcases hx1 with hxP | hxC1
    · rcases hx2 with hxP' | hxC2
      · exact hxP
      · exact False.elim ((Finset.disjoint_left.mp hP2) hxP hxC2)
    · rcases hx2 with hxP | hxC2
      · exact False.elim ((Finset.disjoint_left.mp hP1) hxP hxC1)
      · exact False.elim ((Finset.disjoint_left.mp h12) hxC1 hxC2)
  · intro hxP
    exact ⟨Or.inl hxP, Or.inl hxP⟩

end Omega.GroupUnification
