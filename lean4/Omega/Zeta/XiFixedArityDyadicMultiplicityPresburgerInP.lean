import Mathlib.Tactic
import Omega.Folding.FoldBinDigitDP
import Omega.SPG

namespace Omega.Zeta

/-- Concrete package for the fixed-arity dyadic-multiplicity Presburger classifier. The input
provides the size parameter `m`, the terminal bit, and the Zeckendorf slack digits used by the
linear-time digit DP; the fixed Presburger evaluator then consumes the computed multiplicity. -/
structure FixedArityDyadicMultiplicityPresburgerData where
  Input : Type
  arity : ℕ
  sizeParameter : Input → ℕ
  value : Input → ℕ
  lastBit : Input → Bool
  slackDigits : Input → List Bool
  presburgerEvaluator : ℕ → ℕ → Bool → ℕ → Bool
  language : Input → Prop
  satLanguage : Input → Prop
  satManyOneReduction : Prop
  slackLength_spec :
    ∀ x, (slackDigits x).length = Omega.Folding.foldBinDigitTailLength (sizeParameter x)
  language_spec :
    ∀ x,
      presburgerEvaluator (sizeParameter x) (value x) (lastBit x)
          (Omega.Folding.foldBinDigitDP (slackDigits x) (lastBit x)) = true ↔
        language x
  sat_spec : ∀ x, satLanguage x ↔ language x

namespace FixedArityDyadicMultiplicityPresburgerData

/-- The dyadic multiplicity attached to the current input word, computed by the chapter-local
linear-time digit DP. -/
def dyadicMultiplicity (D : FixedArityDyadicMultiplicityPresburgerData) (x : D.Input) : ℕ :=
  Omega.Folding.foldBinDigitDP (D.slackDigits x) (D.lastBit x)

/-- Fixed-size Presburger evaluation on the fields extracted from the input. -/
def decideLanguage (D : FixedArityDyadicMultiplicityPresburgerData) (x : D.Input) : Bool :=
  D.presburgerEvaluator (D.sizeParameter x) (D.value x) (D.lastBit x) (D.dyadicMultiplicity x)

lemma dyadicMultiplicity_audit (D : FixedArityDyadicMultiplicityPresburgerData) (x : D.Input) :
    D.dyadicMultiplicity x = Omega.Folding.admissibleTailCount (D.slackDigits x) (D.lastBit x) ∧
      Omega.Folding.foldBinDigitDPOperations (D.slackDigits x) ≤
        4 * Omega.Folding.foldBinDigitTailLength (D.sizeParameter x) + 4 ∧
      Omega.Folding.foldBinDigitDPOperations (D.slackDigits x) ≤ 4 * D.sizeParameter x + 4 := by
  simpa [dyadicMultiplicity] using
    Omega.Folding.paper_fold_bin_digit_dp (D.sizeParameter x) (D.lastBit x) (D.slackDigits x)
      (D.slackLength_spec x)

lemma decideLanguage_spec (D : FixedArityDyadicMultiplicityPresburgerData) (x : D.Input) :
    D.decideLanguage x = true ↔ D.language x := by
  simpa [decideLanguage, dyadicMultiplicity] using D.language_spec x

lemma language_polytimeDecidable (D : FixedArityDyadicMultiplicityPresburgerData) :
    Omega.SPG.PolytimeDecidable D.language := by
  refine ⟨D.decideLanguage, trivial, ?_⟩
  intro x
  exact D.decideLanguage_spec x

lemma satLanguage_polytimeDecidable (D : FixedArityDyadicMultiplicityPresburgerData) :
    Omega.SPG.PolytimeDecidable D.satLanguage := by
  rcases D.language_polytimeDecidable with ⟨decideL, hPoly, hSpec⟩
  refine ⟨decideL, hPoly, ?_⟩
  intro x
  constructor
  · intro hx
    exact (D.sat_spec x).2 ((hSpec x).1 hx)
  · intro hx
    exact (hSpec x).2 ((D.sat_spec x).1 hx)

lemma satLanguage_barrier (D : FixedArityDyadicMultiplicityPresburgerData) :
    D.satManyOneReduction → Omega.SPG.PEqualsNP D.satLanguage := by
  intro _hReduction
  have hSat : Omega.SPG.PolytimeDecidable D.satLanguage := D.satLanguage_polytimeDecidable
  exact ⟨Omega.SPG.complement_polytime_decidable hSat, hSat⟩

end FixedArityDyadicMultiplicityPresburgerData

open FixedArityDyadicMultiplicityPresburgerData

/-- Fixed-arity dyadic multiplicities are computed by the linear-time fold-bin digit DP, and the
resulting fixed Presburger predicate is therefore polynomial-time decidable. Any polynomial-time
many-one reduction from `SAT` to that language triggers the chapter-local `P = NP` barrier. -/
theorem paper_xi_fixed_arity_dyadic_multiplicity_presburger_in_p
    (D : FixedArityDyadicMultiplicityPresburgerData) :
    Omega.SPG.PolytimeDecidable D.language ∧
      (D.satManyOneReduction → Omega.SPG.PEqualsNP D.satLanguage) := by
  exact ⟨D.language_polytimeDecidable, D.satLanguage_barrier⟩

end Omega.Zeta
