import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Omega.OperatorAlgebra.FoldJonesBasicConstructionDirectsum

open scoped BigOperators

namespace Omega.OperatorAlgebra

section

variable {Ω X : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype X] [DecidableEq X]

open FoldJonesBasicConstructionDirectsum

/-- The pure-tensor basis surviving the relative tensor-power relations: choose a common fiber
`x`, then a `q`-tuple inside that fiber. -/
def foldRelativeTensorPowerBasis (fold : Ω → X) (q : ℕ) :=
  Σ x : X, Fin q → foldFiber fold x

/-- The concrete `q`-fold fiber product of the fold map. -/
def foldRelativeTensorPowerFiberProduct (fold : Ω → X) (q : ℕ) :=
  {ω : Fin q → Ω // ∀ i j, fold (ω i) = fold (ω j)}

instance (fold : Ω → X) (q : ℕ) : Fintype (foldRelativeTensorPowerBasis fold q) := by
  dsimp [foldRelativeTensorPowerBasis]
  infer_instance

instance (fold : Ω → X) (q : ℕ) : Fintype (foldRelativeTensorPowerFiberProduct fold q) :=
  by
    dsimp [foldRelativeTensorPowerFiberProduct]
    infer_instance

/-- The canonical basis equivalence between same-fiber pure tensors and points of the fiber
product. -/
def foldRelativeTensorPowerToFiberProduct (fold : Ω → X) (q : ℕ) :
    foldRelativeTensorPowerBasis fold q → foldRelativeTensorPowerFiberProduct fold q
  | ⟨x, t⟩ => ⟨fun i => (t i).1, fun i j => (t i).2.trans (t j).2.symm⟩

lemma foldRelativeTensorPowerToFiberProduct_bijective (fold : Ω → X) (q : ℕ) (hq : 1 ≤ q) :
    Function.Bijective (foldRelativeTensorPowerToFiberProduct fold q) := by
  let i0 : Fin q := ⟨0, hq⟩
  constructor
  · intro a b hab
    rcases a with ⟨x, t⟩
    rcases b with ⟨x', t'⟩
    dsimp [foldRelativeTensorPowerToFiberProduct] at hab
    have hfun : (fun i => (t i).1) = fun i => (t' i).1 := congrArg Subtype.val hab
    have hi0 : (t i0).1 = (t' i0).1 := by simpa using congrArg (fun f => f i0) hfun
    have hx : x = x' := by
      calc
        x = fold ((t i0).1) := by simpa using (t i0).2.symm
        _ = fold ((t' i0).1) := by rw [hi0]
        _ = x' := by simpa using (t' i0).2
    subst x'
    have ht : t = t' := by
      funext i
      apply Subtype.ext
      exact congrArg (fun f => f i) hfun
    simpa [ht]
  · intro ω
    refine ⟨⟨fold (ω.1 i0), fun i => ⟨ω.1 i, ω.2 i i0⟩⟩, ?_⟩
    apply Subtype.ext
    rfl

noncomputable def foldRelativeTensorPowerBasisEquivFiberProduct (fold : Ω → X) (q : ℕ)
    (hq : 1 ≤ q) :
    foldRelativeTensorPowerBasis fold q ≃ foldRelativeTensorPowerFiberProduct fold q :=
  Equiv.ofBijective (foldRelativeTensorPowerToFiberProduct fold q)
    (foldRelativeTensorPowerToFiberProduct_bijective fold q hq)

lemma foldRelativeTensorPowerBasis_card (fold : Ω → X) (q : ℕ) :
    Fintype.card (foldRelativeTensorPowerBasis fold q) =
      ∑ x, Fintype.card (foldFiber fold x) ^ q := by
  change Fintype.card (Σ x : X, Fin q → foldFiber fold x) =
    ∑ x, Fintype.card (foldFiber fold x) ^ q
  calc
    Fintype.card (Σ x : X, Fin q → foldFiber fold x)
      = ∑ x, Fintype.card (Fin q → foldFiber fold x) := Fintype.card_sigma
    _ = ∑ x, Fintype.card (foldFiber fold x) ^ q := by
      refine Finset.sum_congr rfl ?_
      intro x hx
      rw [Fintype.card_fun, Fintype.card_fin]

/-- Paper label: `prop:op-algebra-fold-relative-tensor-power-fiber-product`.
In the finite fold model, the relative `q`-fold tensor power has a canonical basis indexed by the
same-fiber `q`-tuples, hence by the `q`-fold fiber product, and its dimension is `∑ₓ d(x)^q`. -/
theorem paper_op_algebra_fold_relative_tensor_power_fiber_product
    (fold : Ω → X) (q : ℕ) (hq : 1 ≤ q) :
    Nonempty (foldRelativeTensorPowerBasis fold q ≃ foldRelativeTensorPowerFiberProduct fold q) ∧
      Fintype.card (foldRelativeTensorPowerBasis fold q) =
        Fintype.card (foldRelativeTensorPowerFiberProduct fold q) ∧
      Fintype.card (foldRelativeTensorPowerBasis fold q) =
        ∑ x, Fintype.card (foldFiber fold x) ^ q := by
  let e := foldRelativeTensorPowerBasisEquivFiberProduct fold q hq
  refine ⟨⟨e⟩, Fintype.card_congr e, foldRelativeTensorPowerBasis_card fold q⟩

end

end Omega.OperatorAlgebra
