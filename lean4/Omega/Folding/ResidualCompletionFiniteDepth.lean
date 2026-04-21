import Omega.Folding.FibKernelBasisFiniteDepth

namespace Omega.Folding

open Omega.EA

/-- Paper label: `cor:fold-residual-completion-finite-depth`. The finite-depth residual
completion map is just the existing `(NF_pr, R)` package, whose uniqueness clause gives
injectivity directly. -/
theorem paper_fold_residual_completion_finite_depth :
    Function.Injective (fun a : DigitCfg => (NF_pr a, R a)) := by
  intro a b h
  have hNF : NF_pr a = NF_pr b := by
    simpa using congrArg Prod.fst h
  have hR : R a = R b := by
    simpa using congrArg Prod.snd h
  exact (paper_fib_kernel_basis_finite_depth 0).2.2.2 a b hNF hR

end Omega.Folding
