import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Omega.POM.ModpDifferenceBinomialBasis

namespace Omega.POM

open scoped fwdDiff

/-- Mod-`2` specialization of the tail binomial-basis normal form package. The data record the
vanishing `b`-th forward difference on the tail starting at `m₀`, a coefficient family supported
below `b`, and the uniqueness of the resulting binomial-basis expansion over `ZMod 2`. -/
structure Mod2DifferenceBinomialBasisData where
  b : ℕ
  m₀ : ℕ
  a : ℕ → ZMod 2
  coeff : ℕ → ZMod 2
  diffKilled : ∀ n, Δ_[1]^[b] (fun m ↦ a (m₀ + m)) n = 0
  coeffZeroAbove : ∀ j, b ≤ j → coeff j = 0
  normalForm : ∀ n, a (m₀ + n) = modpBinomialBasisEval coeff (n + 1) n
  coeffUnique :
    ∀ d : ℕ → ZMod 2,
      (∀ j, b ≤ j → d j = 0) →
      (∀ n, a (m₀ + n) = modpBinomialBasisEval d (n + 1) n) →
        d = coeff

/-- Paper-facing mod-`2` specialization of the mod-`p` difference/binomial-basis package.
    thm:pom-mod2-difference-binomial-basis -/
theorem paper_pom_mod2_difference_binomial_basis (h : Mod2DifferenceBinomialBasisData) :
    (∀ n, Δ_[1]^[h.b] (fun m ↦ h.a (h.m₀ + m)) n = 0) ∧
      ∃! c : ℕ → ZMod 2,
        (∀ j, h.b ≤ j → c j = 0) ∧
          (∀ n, h.a (h.m₀ + n) = modpBinomialBasisEval c (n + 1) n) := by
  refine ⟨h.diffKilled, ?_⟩
  refine ⟨h.coeff, ⟨h.coeffZeroAbove, h.normalForm⟩, ?_⟩
  intro d hd
  exact h.coeffUnique d hd.1 hd.2

end Omega.POM
