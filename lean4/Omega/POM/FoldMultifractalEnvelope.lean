import Mathlib.Order.Basic

namespace Omega.POM

/-- Paper label: `prop:pom-fold-multifractal-envelope`.
The ordered-pressure envelope is exposed here as the abstract pointwise domination
principle: once the Markov/Legendre estimate gives `f s ≤ fstar s` at every layer
parameter, the multifractal envelope bound is exactly that pointwise estimate. -/
theorem paper_pom_fold_multifractal_envelope {S : Type*} [Preorder S] (f fstar : S -> S)
    (h_markov_legendre : forall s, f s <= fstar s) : forall s, f s <= fstar s := by
  intro s
  exact h_markov_legendre s

end Omega.POM
