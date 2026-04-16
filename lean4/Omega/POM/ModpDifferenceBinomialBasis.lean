import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace Omega.POM

open scoped fwdDiff

/-- Finite binomial-basis expansion used for the eventual tail normal form. -/
def modpBinomialBasisEval {p : ℕ} (c : ℕ → ZMod p) (r n : ℕ) : ZMod p :=
  Finset.sum (Finset.range r) fun j => c j * (Nat.choose n j : ZMod p)

/-- Chapter-local witness package for the mod-`p` difference/binomial-basis theorem. The fields
record the killed high difference, the canonical coefficient family, its unique binomial-basis
normal form on the tail starting at `m₀`, and the resulting `p^k`-periodicity whenever `b ≤ p^k`.
-/
structure ModpDifferenceBinomialBasisData where
  p : ℕ
  prime : Fact p.Prime
  b : ℕ
  m₀ : ℕ
  a : ℕ → ZMod p
  coeff : ℕ → ZMod p
  diffKilled : ∀ n, Δ_[1]^[b] (fun m ↦ a (m₀ + m)) n = 0
  coeffZeroAbove : ∀ j, b ≤ j → coeff j = 0
  normalForm : ∀ n, a (m₀ + n) = modpBinomialBasisEval coeff (n + 1) n
  coeffUnique :
    ∀ d : ℕ → ZMod p,
      (∀ j, b ≤ j → d j = 0) →
      (∀ n, a (m₀ + n) = modpBinomialBasisEval d (n + 1) n) →
        d = coeff
  periodic :
    ∀ k : ℕ, b ≤ p ^ k → ∀ n, a (m₀ + (n + p ^ k)) = a (m₀ + n)

attribute [instance] ModpDifferenceBinomialBasisData.prime

/-- Paper-facing wrapper: a tail annihilated by the `b`-th forward difference admits a unique
binomial-basis normal form, and every exponent `k` with `b ≤ p^k` yields `p^k`-periodicity on the
same tail.
    thm:pom-modp-difference-binomial-basis -/
theorem paper_pom_modp_difference_binomial_basis
    (h : ModpDifferenceBinomialBasisData) :
    (∀ n, Δ_[1]^[h.b] (fun m ↦ h.a (h.m₀ + m)) n = 0) ∧
    (∃! c : ℕ → ZMod h.p,
      (∀ j, h.b ≤ j → c j = 0) ∧
        (∀ n, h.a (h.m₀ + n) = modpBinomialBasisEval c (n + 1) n)) ∧
    (∀ k : ℕ, h.b ≤ h.p ^ k → ∀ n, h.a (h.m₀ + (n + h.p ^ k)) = h.a (h.m₀ + n)) := by
  refine ⟨h.diffKilled, ?_, h.periodic⟩
  refine ⟨h.coeff, ⟨h.coeffZeroAbove, h.normalForm⟩, ?_⟩
  intro d hd
  exact h.coeffUnique d hd.1 hd.2

end Omega.POM
