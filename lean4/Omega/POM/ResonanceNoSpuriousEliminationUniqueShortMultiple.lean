import Mathlib.Tactic
import Omega.POM.ResonanceHankelNullIntegralPrincipalization

namespace Omega.POM

/-- Concrete package for the "no spurious elimination" corollary. A short multiplier is encoded by
its coefficient vector on `Fin degreeGap`; `extendShort` pads it to a vector on `Fin n`. The
principalization theorem turns a null-mode coefficient vector into module membership, and the
degree bound `degreeGap ≤ n` makes the padding map injective, yielding uniqueness. -/
structure ResonanceNoSpuriousEliminationData where
  principalization : ResonanceHankelNullIntegralPrincipalizationData
  degreeGap : ℕ
  hgap : degreeGap ≤ principalization.n
  Bcoeffs : Fin principalization.n → ℤ
  nullmodeCoeff : Bcoeffs ∈ principalization.nullModeKernel
  witness : Fin degreeGap → ℤ
  witness_eq_Bcoeffs :
    (fun i : Fin principalization.n =>
      if h : i.1 < degreeGap then witness ⟨i.1, h⟩ else 0) = Bcoeffs

namespace ResonanceNoSpuriousEliminationData

/-- Padding of a short coefficient vector to length `n`. -/
def extendShort (D : ResonanceNoSpuriousEliminationData) (Q : Fin D.degreeGap → ℤ) :
    Fin D.principalization.n → ℤ :=
  fun i => if h : i.1 < D.degreeGap then Q ⟨i.1, h⟩ else 0

/-- The coefficient vector `Q` is a valid short multiple when principalization places `B` in the
multiple module and the padded coefficients recover `B`. -/
def IsShortMultiple (D : ResonanceNoSpuriousEliminationData) (Q : Fin D.degreeGap → ℤ) : Prop :=
  D.Bcoeffs ∈ D.principalization.multipleModule ∧ D.extendShort Q = D.Bcoeffs

/-- Paper conclusion: there is a unique short coefficient vector whose padded coefficients recover
`B`. -/
def existsUniqueShortMultiple (D : ResonanceNoSpuriousEliminationData) : Prop :=
  ∃! Q : Fin D.degreeGap → ℤ, D.IsShortMultiple Q

lemma extendShort_injective (D : ResonanceNoSpuriousEliminationData) :
    Function.Injective D.extendShort := by
  intro Q₁ Q₂ hQ
  ext i
  have hEval := congrArg (fun f => f ⟨i.1, lt_of_lt_of_le i.is_lt D.hgap⟩) hQ
  simpa [extendShort, i.is_lt] using hEval

end ResonanceNoSpuriousEliminationData

open ResonanceNoSpuriousEliminationData

/-- Paper label: `cor:pom-resonance-no-spurious-elimination-unique-short-multiple`. -/
theorem paper_pom_resonance_no_spurious_elimination_unique_short_multiple
    (D : ResonanceNoSpuriousEliminationData) : D.existsUniqueShortMultiple := by
  have hPrincipal : D.principalization.nullModesEqMultiples :=
    paper_pom_resonance_hankel_null_integral_principalization D.principalization
  have hEq : D.principalization.nullModeKernel = D.principalization.multipleModule := hPrincipal
  have hBmultiple : D.Bcoeffs ∈ D.principalization.multipleModule := by
    simpa [hEq] using D.nullmodeCoeff
  refine ⟨D.witness, ?_, ?_⟩
  · exact ⟨hBmultiple, by simpa [extendShort] using D.witness_eq_Bcoeffs⟩
  · intro Q hQ
    exact D.extendShort_injective (hQ.2.trans D.witness_eq_Bcoeffs.symm)

end Omega.POM
