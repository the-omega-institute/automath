import Mathlib.Tactic

namespace Omega.Zeta

/-- Chapter-local package for the left-c.e./dyadic-density theorem. The structure records the
stagewise left-c.e. construction of a decidable set of dyadic density `α`, the rationality
criterion for DFA-recognizable dyadic densities, and the irrational `Ω` example used to rule out
constant-memory recognition. -/
structure LeftCEDyadicDensityData where
  Word : Type
  Density : Type
  Salpha : Word → Prop
  SOmega : Word → Prop
  alpha : Density
  alphaLeftCE : Prop
  dfaRecognizable : (Word → Prop) → Prop
  dyadicDensity : (Word → Prop) → Density → Prop
  rationalDensity : Density → Prop
  leftCERealizedByDecidableSet :
    alphaLeftCE → Nonempty (DecidablePred Salpha) ∧ dyadicDensity Salpha alpha
  dfaDyadicDensityRational :
    ∀ S β, dfaRecognizable S → dyadicDensity S β → rationalDensity β
  omegaDyadicDensity : dyadicDensity SOmega alpha
  omegaIrrational : ¬ rationalDensity alpha

/-- Paper-facing wrapper for the left-c.e./dyadic-density package: a left-c.e. density is realized
as the dyadic density of a decidable set, every DFA-recognizable dyadic density is rational, and
therefore the `Ω` example is not DFA-recognizable.
    thm:zeta-syntax-leftce-dyadic-density -/
theorem paper_zeta_syntax_leftce_dyadic_density (D : LeftCEDyadicDensityData) :
    (D.alphaLeftCE → Nonempty (DecidablePred D.Salpha) ∧ D.dyadicDensity D.Salpha D.alpha) ∧
      (∀ S β, D.dfaRecognizable S → D.dyadicDensity S β → D.rationalDensity β) ∧
      ¬ D.dfaRecognizable D.SOmega := by
  refine ⟨D.leftCERealizedByDecidableSet, D.dfaDyadicDensityRational, ?_⟩
  intro hDFA
  exact D.omegaIrrational (D.dfaDyadicDensityRational D.SOmega D.alpha hDFA D.omegaDyadicDensity)

end Omega.Zeta
