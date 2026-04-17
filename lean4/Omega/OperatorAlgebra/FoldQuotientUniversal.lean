import Omega.Folding.FiberArithmeticProperties

namespace Omega

/-- The fold map realizes `X m` as the quotient of `Word m` by the fold setoid, and every map on
words whose fibers are exactly the fold fibers factors uniquely through `Fold`.
    prop:op-algebra-fold-quotient-universal -/
theorem paper_op_algebra_fold_quotient_universal {Z : Type*} (m : Nat) (f : Omega.Word m → Z)
    (hf : ∀ a a', f a = f a' ↔ Omega.Fold a = Omega.Fold a') :
    ∃! fbar : Omega.X m → Z, ∀ a, f a = fbar (Omega.Fold a) := by
  classical
  let fquot : Quotient (Omega.foldSetoid m) → Z :=
    Quotient.lift f (fun a a' h => (hf a a').2 h)
  let fbar : Omega.X m → Z := fun x => fquot ((Omega.foldQuotientEquiv m).symm x)
  have hfactor : ∀ a, f a = fbar (Omega.Fold a) := by
    intro a
    dsimp [fbar, fquot]
    let q : Quotient (Omega.foldSetoid m) := Quotient.mk (Omega.foldSetoid m) a
    have hq : (Omega.foldQuotientEquiv m).symm (Omega.Fold a) = q := by
      apply (Omega.foldQuotientEquiv m).injective
      refine (Equiv.apply_symm_apply (Omega.foldQuotientEquiv m) (Omega.Fold a)).trans ?_
      change Omega.Fold a = Quotient.lift Omega.Fold (fun _ _ h => h) q
      rfl
    rw [hq]
    change f a = Quotient.lift f (fun a a' h => (hf a a').2 h) q
    rfl
  refine ⟨fbar, ?_, ?_⟩
  · exact hfactor
  · intro g hg
    funext x
    obtain ⟨a, rfl⟩ := Omega.Fold_surjective m x
    exact (hg a).symm.trans (hfactor a)

end Omega
