import Mathlib.Tactic

namespace Omega.Zeta

/-- Galois-stable subsets of the six Weierstrass points, encoded by the four orbit choices:
`∞`, `(0,0)`, `(1,0)`, and the irreducible cubic orbit. -/
structure xi_leyang_jacobian_rational_2torsion_complete_orbitCode where
  infinity : Bool
  zeroRoot : Bool
  oneRoot : Bool
  cubicOrbit : Bool
  deriving DecidableEq

/-- Pointwise xor of orbit codes. -/
def xi_leyang_jacobian_rational_2torsion_complete_xorCode
    (a b : xi_leyang_jacobian_rational_2torsion_complete_orbitCode) :
    xi_leyang_jacobian_rational_2torsion_complete_orbitCode where
  infinity := Bool.xor a.infinity b.infinity
  zeroRoot := Bool.xor a.zeroRoot b.zeroRoot
  oneRoot := Bool.xor a.oneRoot b.oneRoot
  cubicOrbit := Bool.xor a.cubicOrbit b.cubicOrbit

/-- Complement of an orbit code, representing the hyperelliptic complement relation. -/
def xi_leyang_jacobian_rational_2torsion_complete_complementCode
    (a : xi_leyang_jacobian_rational_2torsion_complete_orbitCode) :
    xi_leyang_jacobian_rational_2torsion_complete_orbitCode where
  infinity := !a.infinity
  zeroRoot := !a.zeroRoot
  oneRoot := !a.oneRoot
  cubicOrbit := !a.cubicOrbit

/-- The zero divisor class. -/
def xi_leyang_jacobian_rational_2torsion_complete_zeroClass :
    xi_leyang_jacobian_rational_2torsion_complete_orbitCode where
  infinity := false
  zeroRoot := false
  oneRoot := false
  cubicOrbit := false

/-- The marked class `e₀=[(0,0)-∞]`, encoded by the subset `{∞,(0,0)}`. -/
def xi_leyang_jacobian_rational_2torsion_complete_markedE0 :
    xi_leyang_jacobian_rational_2torsion_complete_orbitCode where
  infinity := true
  zeroRoot := true
  oneRoot := false
  cubicOrbit := false

/-- The marked class `e₁=[(1,0)-∞]`, encoded by the subset `{∞,(1,0)}`. -/
def xi_leyang_jacobian_rational_2torsion_complete_markedE1 :
    xi_leyang_jacobian_rational_2torsion_complete_orbitCode where
  infinity := true
  zeroRoot := false
  oneRoot := true
  cubicOrbit := false

/-- Even cardinality condition for stable orbit codes.  The cubic orbit has odd size, so parity is
the xor of the four orbit choices. -/
def xi_leyang_jacobian_rational_2torsion_complete_stableEven
    (a : xi_leyang_jacobian_rational_2torsion_complete_orbitCode) : Prop :=
  Bool.xor (Bool.xor (Bool.xor a.infinity a.zeroRoot) a.oneRoot) a.cubicOrbit = false

/-- Equality modulo the complement relation on even Weierstrass subsets. -/
def xi_leyang_jacobian_rational_2torsion_complete_sameClass
    (a b : xi_leyang_jacobian_rational_2torsion_complete_orbitCode) : Prop :=
  a = b ∨ xi_leyang_jacobian_rational_2torsion_complete_complementCode a = b

/-- Span of the two marked rational `2`-torsion classes. -/
def xi_leyang_jacobian_rational_2torsion_complete_markedSpan
    (useE0 useE1 : Bool) :
    xi_leyang_jacobian_rational_2torsion_complete_orbitCode :=
  xi_leyang_jacobian_rational_2torsion_complete_xorCode
    (if useE0 then
      xi_leyang_jacobian_rational_2torsion_complete_markedE0
    else
      xi_leyang_jacobian_rational_2torsion_complete_zeroClass)
    (if useE1 then
      xi_leyang_jacobian_rational_2torsion_complete_markedE1
    else
      xi_leyang_jacobian_rational_2torsion_complete_zeroClass)

/-- The two marked classes are nonzero, distinct, and give four distinct classes modulo complement. -/
def xi_leyang_jacobian_rational_2torsion_complete_markedClassesIndependent : Prop :=
  ∀ a b a' b' : Bool,
    xi_leyang_jacobian_rational_2torsion_complete_sameClass
      (xi_leyang_jacobian_rational_2torsion_complete_markedSpan a b)
      (xi_leyang_jacobian_rational_2torsion_complete_markedSpan a' b') →
      a = a' ∧ b = b'

/-- Every Galois-stable even subset class is in the span of `e₀` and `e₁`. -/
def xi_leyang_jacobian_rational_2torsion_complete_everyRationalTwoTorsionGenerated :
    Prop :=
  ∀ a : xi_leyang_jacobian_rational_2torsion_complete_orbitCode,
    xi_leyang_jacobian_rational_2torsion_complete_stableEven a →
      ∃ useE0 useE1 : Bool,
        xi_leyang_jacobian_rational_2torsion_complete_sameClass a
          (xi_leyang_jacobian_rational_2torsion_complete_markedSpan useE0 useE1)

private theorem xi_leyang_jacobian_rational_2torsion_complete_independent :
    xi_leyang_jacobian_rational_2torsion_complete_markedClassesIndependent := by
  intro a b a' b' h
  cases a <;> cases b <;> cases a' <;> cases b' <;>
    simp [xi_leyang_jacobian_rational_2torsion_complete_sameClass,
      xi_leyang_jacobian_rational_2torsion_complete_markedSpan,
      xi_leyang_jacobian_rational_2torsion_complete_xorCode,
      xi_leyang_jacobian_rational_2torsion_complete_complementCode,
      xi_leyang_jacobian_rational_2torsion_complete_markedE0,
      xi_leyang_jacobian_rational_2torsion_complete_markedE1,
      xi_leyang_jacobian_rational_2torsion_complete_zeroClass] at h ⊢

private theorem xi_leyang_jacobian_rational_2torsion_complete_generated :
    xi_leyang_jacobian_rational_2torsion_complete_everyRationalTwoTorsionGenerated := by
  intro a ha
  rcases a with ⟨a0, a1, a2, a3⟩
  cases a0 <;> cases a1 <;> cases a2 <;> cases a3 <;>
    simp [xi_leyang_jacobian_rational_2torsion_complete_stableEven,
      xi_leyang_jacobian_rational_2torsion_complete_sameClass,
      xi_leyang_jacobian_rational_2torsion_complete_markedSpan,
      xi_leyang_jacobian_rational_2torsion_complete_xorCode,
      xi_leyang_jacobian_rational_2torsion_complete_complementCode,
      xi_leyang_jacobian_rational_2torsion_complete_markedE0,
      xi_leyang_jacobian_rational_2torsion_complete_markedE1,
      xi_leyang_jacobian_rational_2torsion_complete_zeroClass] at ha ⊢

/-- Paper label: `thm:xi-leyang-jacobian-rational-2torsion-complete`. -/
theorem paper_xi_leyang_jacobian_rational_2torsion_complete :
    xi_leyang_jacobian_rational_2torsion_complete_markedClassesIndependent ∧
      xi_leyang_jacobian_rational_2torsion_complete_everyRationalTwoTorsionGenerated := by
  exact ⟨xi_leyang_jacobian_rational_2torsion_complete_independent,
    xi_leyang_jacobian_rational_2torsion_complete_generated⟩

end Omega.Zeta
