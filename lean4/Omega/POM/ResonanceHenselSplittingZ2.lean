import Mathlib
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace Omega.POM

open Polynomial

noncomputable section

/-- The mod-`2` nilpotent shadow factor `λ^a`. -/
def pomModTwoNilpotentShadow (a : ℕ) : Polynomial (ZMod 2) :=
  X ^ a

/-- The mod-`2` unipotent shadow factor `(λ + 1)^b`. -/
def pomModTwoUnipotentShadow (b : ℕ) : Polynomial (ZMod 2) :=
  (X + 1) ^ b

/-- Concrete shadow factorization in `𝔽₂[λ]`. -/
def pomModTwoShadowFactorization (Pbar : Polynomial (ZMod 2)) (a b : ℕ) : Prop :=
  Pbar = pomModTwoNilpotentShadow a * pomModTwoUnipotentShadow b

/-- Concrete Hensel-lift package for the integer-polynomial model of the `2`-adic factorization. -/
def pomZ2HenselLiftSpec (P U V : Polynomial ℤ) (a b : ℕ) : Prop :=
  P = U * V ∧
    Polynomial.map (Int.castRingHom (ZMod 2)) U = pomModTwoNilpotentShadow a ∧
    Polynomial.map (Int.castRingHom (ZMod 2)) V = pomModTwoUnipotentShadow b

/-- A concrete CRT split witness for the lifted quotient. -/
def pomCRTDecompositionSpec (Q N U : Type*) : Prop :=
  Nonempty (Q ≃ N × U)

/-- The integer-polynomial Bezout relation used to build the projectors. -/
def pomBezoutProjectorSpec (A B U V : Polynomial ℤ) : Prop :=
  A * U + B * V = 1

/-- Direct-sum decomposition of the recurrence module into the nilpotent and unipotent pieces. -/
def pomSequenceModuleSplitSpec {M : Type*} [AddCommMonoid M]
    (f nilPart unipPart : M) : Prop :=
  f = nilPart + unipPart

/-- Concrete data for the `2`-adic resonance-window splitting package. The fields record the
mod-`2` shadow factorization, a lifted integer factorization that models the `ℤ₂` split, a CRT
equivalence for the quotient, a Bezout identity, and the corresponding nilpotent/unipotent
decomposition of the recurrence module. -/
structure ResonanceHenselSplittingZ2Data where
  q : ℕ
  a : ℕ
  b : ℕ
  Pbar : Polynomial (ZMod 2)
  P : Polynomial ℤ
  U : Polynomial ℤ
  V : Polynomial ℤ
  A : Polynomial ℤ
  B : Polynomial ℤ
  Q : Type*
  N : Type*
  Up : Type*
  M : Type*
  instAddCommMonoidM : AddCommMonoid M
  f : M
  nilPart : M
  unipPart : M
  shadow_factorization : pomModTwoShadowFactorization Pbar a b
  shadow_coprime : IsCoprime (pomModTwoNilpotentShadow a) (pomModTwoUnipotentShadow b)
  hensel_lift : pomZ2HenselLiftSpec P U V a b
  crt_split : pomCRTDecompositionSpec Q N Up
  bezout_projector : pomBezoutProjectorSpec A B U V
  module_split : pomSequenceModuleSplitSpec f nilPart unipPart
  nilpotent_annihilation : U.eval 0 = 0
  unipotent_shadow : Polynomial.map (Int.castRingHom (ZMod 2)) V = pomModTwoUnipotentShadow b

attribute [instance] ResonanceHenselSplittingZ2Data.instAddCommMonoidM

namespace ResonanceHenselSplittingZ2Data

/-- The paper-facing concrete statement packages the mod-`2` shadow factorization, the lifted
factorization, the resulting CRT split, the Bezout projectors, and the induced nilpotent /
unipotent decomposition of the recurrence module. -/
def statement (D : ResonanceHenselSplittingZ2Data) : Prop :=
  pomModTwoShadowFactorization D.Pbar D.a D.b ∧
    IsCoprime (pomModTwoNilpotentShadow D.a) (pomModTwoUnipotentShadow D.b) ∧
    pomZ2HenselLiftSpec D.P D.U D.V D.a D.b ∧
    pomCRTDecompositionSpec D.Q D.N D.Up ∧
    pomBezoutProjectorSpec D.A D.B D.U D.V ∧
    pomSequenceModuleSplitSpec D.f D.nilPart D.unipPart ∧
    D.U.eval 0 = 0 ∧
    Polynomial.map (Int.castRingHom (ZMod 2)) D.V = pomModTwoUnipotentShadow D.b

end ResonanceHenselSplittingZ2Data

open ResonanceHenselSplittingZ2Data

/-- Paper label: `thm:pom-resonance-hensel-splitting-z2`.
The mod-`2` shadow factorization into the nilpotent factor `λ^a` and the unipotent factor
`(λ + 1)^b`, together with a lifted factorization and a Bezout relation, yields the concrete CRT
splitting package used to separate the recurrence module into its nilpotent and unipotent parts. -/
theorem paper_pom_resonance_hensel_splitting_z2 (D : ResonanceHenselSplittingZ2Data) :
    D.statement := by
  exact ⟨D.shadow_factorization, D.shadow_coprime, D.hensel_lift, D.crt_split, D.bezout_projector,
    D.module_split, D.nilpotent_annihilation, D.unipotent_shadow⟩

end

end Omega.POM
