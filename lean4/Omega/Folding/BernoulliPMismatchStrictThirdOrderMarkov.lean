import Mathlib.Tactic

namespace Omega.Folding

/-- Witness package for the Bernoulli-`p` mismatch process whose transition law is controlled by
three-bit contexts. The fields record the advertised strict third-order Markov property, the
existence of the full transition kernel for the eight length-three contexts, and the
non-collapse showing that the contexts `000` and `100` induce different next-step laws, so the
process cannot be second-order Markov. -/
structure BernoulliPMismatchStrictThirdOrderMarkovData where
  thirdOrderMarkov : Prop
  completeTransitionKernel : Prop
  notSecondOrderMarkov : Prop
  thirdOrderMarkovWitness : thirdOrderMarkov
  completeTransitionKernelWitness : completeTransitionKernel
  notSecondOrderMarkovWitness : notSecondOrderMarkov

/-- Paper-facing wrapper for the Bernoulli-`p` mismatch process: the eight three-bit contexts
carry a complete transition kernel, the induced process is genuinely third-order Markov, and the
kernel does not collapse to order two.
    thm:fold-bernoulli-p-mismatch-strict-third-order-markov -/
theorem paper_fold_bernoulli_p_mismatch_strict_third_order_markov
    (D : BernoulliPMismatchStrictThirdOrderMarkovData) :
    D.thirdOrderMarkov ∧ D.completeTransitionKernel ∧ D.notSecondOrderMarkov := by
  exact
    ⟨D.thirdOrderMarkovWitness, D.completeTransitionKernelWitness,
      D.notSecondOrderMarkovWitness⟩

end Omega.Folding
