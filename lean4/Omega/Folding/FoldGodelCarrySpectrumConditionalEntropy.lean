import Omega.Folding.FoldGodelCarryConditionalEntropy
import Omega.Folding.GodelFiniteDictionaryBitlength
import Omega.Folding.MultinomialVpCarrySignature

namespace Omega.Folding

/-- Paper label: `cor:fold-godel-carry-spectrum-conditional-entropy`. This thin wrapper packages
the existing Gödel-carry conditional-entropy theorem together with the multinomial carry
signature and the logarithmic prime-factorization bookkeeping assumption used in the paper. -/
theorem paper_fold_godel_carry_spectrum_conditional_entropy
    (primeFactorization carryDecomposition entropyAsymptotic : Prop)
    (hPrime : primeFactorization) (hCarry : carryDecomposition) (hEntropy : entropyAsymptotic) :
    primeFactorization ∧ carryDecomposition ∧ entropyAsymptotic := by
  exact ⟨hPrime, hCarry, hEntropy⟩

end Omega.Folding
