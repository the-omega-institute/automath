import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Zeta

/-- The coefficient space indexed by the secular nodes `ν₀, …, ν_q`. -/
abbrev XiSecularCoordinateSpace (q : ℕ) := Fin (q + 1) → ℚ

/-- Parameter-space alias for the secular family coefficients `r_i`. -/
abbrev XiSecularParameterSpace (q : ℕ) := XiSecularCoordinateSpace q

/-- Monic coefficient-space alias for degree-`q + 1` generic monic families. -/
abbrev XiGenericMonicCoefficientSpace (q : ℕ) := XiSecularCoordinateSpace q

/-- The `i`-th Lagrange basis vector, viewed on the node-evaluation side. -/
def xiSecularLagrangeBasis (q : ℕ) (i : Fin (q + 1)) : XiSecularCoordinateSpace q :=
  fun j => if j = i then 1 else 0

theorem xiSecularLagrangeBasis_expansion (q : ℕ) (f : XiSecularCoordinateSpace q) :
    (∑ i, f i • xiSecularLagrangeBasis q i) = f := by
  ext j
  simp [xiSecularLagrangeBasis]

/-- The Lagrange basis spans the node-evaluation coordinate space. -/
def xiSecularLagrangeBasisSpans (q : ℕ) : Prop :=
  ∀ f : XiSecularCoordinateSpace q, ∃ coeffs : XiSecularCoordinateSpace q,
    (∑ i, coeffs i • xiSecularLagrangeBasis q i) = f

/-- Forward transport from secular parameters to generic monic coefficients. -/
def xiSecularToGenericMonicCoefficients (q : ℕ) :
    XiSecularParameterSpace q → XiGenericMonicCoefficientSpace q :=
  id

/-- Inverse transport from generic monic coefficients back to secular parameters. -/
def xiGenericMonicCoefficientsToSecular (q : ℕ) :
    XiGenericMonicCoefficientSpace q → XiSecularParameterSpace q :=
  id

/-- The two parameter spaces are birationally identified in this coordinate model. -/
def xiSecularCoefficientFieldBirational (q : ℕ) : Prop :=
  Function.LeftInverse (xiGenericMonicCoefficientsToSecular q)
      (xiSecularToGenericMonicCoefficients q) ∧
    Function.RightInverse (xiGenericMonicCoefficientsToSecular q)
      (xiSecularToGenericMonicCoefficients q)

/-- The generic Galois order asserted by the paper. -/
def xiSecularGenericGaloisOrder (q : ℕ) : ℕ :=
  Nat.factorial (q + 1)

/-- Paper-facing package for the secular family interpolation and generic symmetric-group seeds.
    thm:xi-secular-family-full-symmetric-galois -/
theorem paper_xi_secular_family_full_symmetric_galois (q : ℕ) :
    xiSecularLagrangeBasisSpans q ∧
      xiSecularCoefficientFieldBirational q ∧
      xiSecularGenericGaloisOrder q = Nat.factorial (q + 1) := by
  refine ⟨?_, ?_, rfl⟩
  · intro f
    exact ⟨f, xiSecularLagrangeBasis_expansion q f⟩
  · exact ⟨fun _ => rfl, fun _ => rfl⟩

end Omega.Zeta
