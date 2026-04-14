import Omega.CircleDimension.CircleDim

namespace Omega.CircleDimension

/-- Paper-facing seed for the uniqueness of circle dimension under the axioms from
    `thm:cdim-axiomatic-rigidity`. -/
theorem paper_cdim_axiomatic_rigidity_seeds (f : Nat → Nat → Nat)
    (hAdd : ∀ a b c d, f (a + b) (c + d) = f a c + f b d)
    (hNorm : f 1 0 = 1)
    (hFin : ∀ t, f 0 t = 0) :
    ∀ n t, f n t = circleDim n t :=
  paper_circleDim_axiomatic_rigidity f hAdd hNorm hFin

end Omega.CircleDimension
