import Mathlib.Data.Finset.Basic
import Mathlib.Tactic
import Omega.Zeta.LeftCEDyadicDensity

namespace Omega.Zeta

/-- Finite-state wrapper for the regular prefix-free Kraft rationality theorem. The finite support
data record a concrete prefix-length audit, while the dyadic-density package supplies the DFA
rationality criterion applied to the Kraft sum. -/
structure RegularPrefixfreeKraftData where
  densityData : LeftCEDyadicDensityData
  code : densityData.Word → Prop
  prefixLengths : Finset ℕ
  acceptingStateCount : ℕ
  kraftSum : densityData.Density
  prefixLengthCount : prefixLengths.card = acceptingStateCount
  regularCode : densityData.dfaRecognizable code
  kraftDensity : densityData.dyadicDensity code kraftSum

/-- The Kraft sum is rational because it is realized as the dyadic density of a DFA-recognizable
prefix-free regular language. -/
def RegularPrefixfreeKraftData.kraftSumRational (D : RegularPrefixfreeKraftData) : Prop :=
  D.densityData.rationalDensity D.kraftSum

/-- Paper-facing regular prefix-free Kraft rationality wrapper: the finite prefix-length audit
keeps the language visibly finite-state, and the existing left-c.e./dyadic-density theorem then
forces the start-state probability, hence the Kraft sum, to be rational.
    prop:zeta-syntax-regular-prefixfree-kraft-rational -/
theorem paper_zeta_syntax_regular_prefixfree_kraft_rational (D : RegularPrefixfreeKraftData) :
    D.kraftSumRational := by
  exact
    (paper_zeta_syntax_leftce_dyadic_density D.densityData).2.1
      D.code D.kraftSum D.regularCode D.kraftDensity

end Omega.Zeta
