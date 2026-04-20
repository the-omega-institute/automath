import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.GroupTheory.Perm.Sign
import Omega.OperatorAlgebra.FoldFiberNormalizerWreath

namespace Omega.OperatorAlgebra

open scoped BigOperators

/-- The hidden factor in the fold-normalizer splitting: keep the fiberwise permutations and reset
the visible permutation to the identity. -/
def hiddenFactor {m : ℕ} (d : Fin m → ℕ) (τ : FoldFiberNormalizer d) : FoldFiberNormalizer d :=
  (visibleIdentity d, τ.2)

/-- Restrict the visible permutation to the odd fibers, which are stable because the visible
component preserves `d`. -/
def oddFiberVisiblePerm {m : ℕ} (d : Fin m → ℕ) (τ : FoldFiberNormalizer d) :
    Equiv.Perm { x : Fin m // Odd (d x) } :=
  τ.1.1.subtypePerm fun x => by
    simpa [τ.1.2 x]

/-- The visible sign contributed by permuting odd-cardinality blocks. -/
def visibleOddBlockSign {m : ℕ} (d : Fin m → ℕ) (τ : FoldFiberNormalizer d) : ℤˣ :=
  Equiv.Perm.sign (oddFiberVisiblePerm d τ)

/-- The product of the fiberwise permutation signs. -/
noncomputable def hiddenFiberProductSign {m : ℕ} (d : Fin m → ℕ) (τ : FoldFiberNormalizer d) :
    ℤˣ :=
  ∏ x, Equiv.Perm.sign (τ.2 x)

/-- Total sign obtained from the visible-section/hidden-factor splitting. -/
noncomputable def foldFiberNormalizerSign {m : ℕ} (d : Fin m → ℕ) (τ : FoldFiberNormalizer d) :
    ℤˣ :=
  visibleOddBlockSign d (visibleSection d (visibleProjection d τ)) *
    hiddenFiberProductSign d (hiddenFactor d τ)

@[simp] theorem hiddenFactor_snd {m : ℕ} (d : Fin m → ℕ) (τ : FoldFiberNormalizer d) :
    (hiddenFactor d τ).2 = τ.2 :=
  rfl

@[simp] theorem visibleProjection_visibleSection_visibleProjection {m : ℕ} (d : Fin m → ℕ)
    (τ : FoldFiberNormalizer d) :
    visibleProjection d (visibleSection d (visibleProjection d τ)) = visibleProjection d τ :=
  rfl

/-- In the fold-normalizer proxy, the global sign factors as the odd-block visible sign times the
product of the hidden fiberwise signs.
    prop:op-algebra-fold-lift-global-sign-factorization -/
theorem paper_op_algebra_fold_lift_global_sign_factorization :
    ∀ {m : ℕ} (d : Fin m → ℕ) (τ : FoldFiberNormalizer d),
      foldFiberNormalizerSign d τ = visibleOddBlockSign d τ * hiddenFiberProductSign d τ := by
  intro m d τ
  simp [foldFiberNormalizerSign, hiddenFactor, visibleOddBlockSign, hiddenFiberProductSign,
    oddFiberVisiblePerm, visibleProjection, visibleSection]

end Omega.OperatorAlgebra
