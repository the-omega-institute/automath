import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Omega.Zeta.BooleanDisjointnessZetaLDLT
import Omega.Zeta.BooleanTwoLayerSmithNormalForm

namespace Omega.Zeta

/-- The symbolic inverse entry on the cover locus `U ∪ V = [q]`. -/
def booleanTwoLayerInverseCoverEntry (q : ℕ) (U V : BooleanSubset q) : ℤ :=
  if U ∪ V = Finset.univ then (-1 : ℤ) ^ (U ∩ V).card else 0

/-- The symbolic adjugate entry on the cover locus `U ∪ V = [q]`. -/
def booleanTwoLayerAdjugateCoverEntry (q : ℕ) (a b : ℤ) (U V : BooleanSubset q) : ℤ :=
  if U ∪ V = Finset.univ then a * (a - b) ^ (2 ^ q - 2) * (-1 : ℤ) ^ (U ∩ V).card else 0

/-- The exceptional origin entry in the inverse template. -/
def booleanTwoLayerInverseOriginEntry (_a b : ℤ) : ℤ :=
  -b

/-- The exceptional origin entry in the adjugate template. -/
def booleanTwoLayerAdjugateOriginEntry (q : ℕ) (a b : ℤ) : ℤ :=
  -b * (a - b) ^ (2 ^ q - 2)

/-- Each coordinate of a cover pair has three states: only in `U`, only in `V`, or in both. -/
def booleanTwoLayerCoverCard (q : ℕ) : ℕ :=
  Fintype.card (Fin q → Fin 3)

/-- The adjugate template has the whole cover locus plus the exceptional origin position. -/
def booleanTwoLayerAdjugateSupportCount (q : ℕ) : ℕ :=
  booleanTwoLayerCoverCard q + 1

/-- Paper-facing package for the complement-cover support law and the symbolic adjugate sparsity
count. The `ζ/μ` factorization comes from the Boolean disjointness package, the first Smith block
from the two-layer Smith normal-form wrapper, and the support count is the `3^q` cover locus plus
the exceptional origin entry.
    thm:xi-boolean-two-layer-inverse-support-law -/
def BooleanTwoLayerInverseSupportLaw (q : ℕ) (a b : ℤ) : Prop :=
  booleanDisjointnessZetaFactorization q ∧
    booleanDisjointnessMobiusCongruence q ∧
    booleanTwoLayerKernelDiagonal (Int.natAbs a) (Int.natAbs b) (2 ^ q - 2) =
      Int.natAbs a :: (Int.natAbs a - Int.natAbs b) ::
        List.replicate (2 ^ q - 2) (Int.natAbs a - Int.natAbs b) ∧
    booleanTwoLayerSmithDiagonal (Int.natAbs a) (Int.natAbs b) (2 ^ q - 2) =
      Nat.gcd (Int.natAbs a) (Int.natAbs a - Int.natAbs b) ::
        Nat.lcm (Int.natAbs a) (Int.natAbs a - Int.natAbs b) ::
          List.replicate (2 ^ q - 2) (Int.natAbs a - Int.natAbs b) ∧
    Nat.gcd (Int.natAbs a) (Int.natAbs a - Int.natAbs b) *
        Nat.lcm (Int.natAbs a) (Int.natAbs a - Int.natAbs b) =
      Int.natAbs a * (Int.natAbs a - Int.natAbs b) ∧
    (∀ U V, U ∪ V = Finset.univ → booleanTwoLayerInverseCoverEntry q U V = (-1 : ℤ) ^ (U ∩ V).card) ∧
    booleanTwoLayerInverseOriginEntry a b = -b ∧
    booleanTwoLayerAdjugateOriginEntry q a b = -b * (a - b) ^ (2 ^ q - 2) ∧
    booleanTwoLayerCoverCard q = 3 ^ q ∧
    booleanTwoLayerAdjugateSupportCount q = 3 ^ q + 1

theorem paper_xi_boolean_two_layer_inverse_support_law (q : ℕ) (hq : 2 ≤ q) (a b : ℤ) :
    BooleanTwoLayerInverseSupportLaw q a b := by
  have hLDLT := paper_xi_disjointness_boolean_zeta_ldlt q hq
  rcases
      paper_xi_boolean_two_layer_smith_normal_form (Int.natAbs a) (Int.natAbs b) (2 ^ q - 2) with
    ⟨_, _, hKernel, hSmith, hProd⟩
  refine ⟨hLDLT.1, hLDLT.2, hKernel, hSmith, hProd, ?_, rfl, rfl, ?_, ?_⟩
  · intro U V hUV
    simp [booleanTwoLayerInverseCoverEntry, hUV]
  · simp [booleanTwoLayerCoverCard]
  · simp [booleanTwoLayerAdjugateSupportCount, booleanTwoLayerCoverCard]

end Omega.Zeta
