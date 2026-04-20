import Mathlib

namespace Omega.OperatorAlgebra

noncomputable section

/-- A visible value is reached by `Fold` if it lies in the image of the source space. -/
def FoldValueReached {Ω X : Type} (Fold : Ω → X) (x : X) : Prop :=
  ∃ ω, Fold ω = x

/-- The visible map induced by a source permutation preserving the fold fibers. Outside the actual
image of `Fold`, it acts as the identity. -/
noncomputable def inducedFoldPermFun {Ω X : Type} (Fold : Ω → X) (σ : Equiv.Perm Ω) (x : X) : X :=
  by
    classical
    exact
      if hx : FoldValueReached Fold x then
        let ω := Classical.choose hx
        Fold (σ ω)
      else
        x

lemma inducedFoldPermFun_apply {Ω X : Type} (Fold : Ω → X) (σ : Equiv.Perm Ω)
    (hσ : ∀ ω ω', Fold ω = Fold ω' ↔ Fold (σ ω) = Fold (σ ω')) (ω : Ω) :
    inducedFoldPermFun Fold σ (Fold ω) = Fold (σ ω) := by
  classical
  have hx : FoldValueReached Fold (Fold ω) := ⟨ω, rfl⟩
  have hchoose : Fold (Classical.choose hx) = Fold ω :=
    Classical.choose_spec hx
  have htransport : Fold (σ (Classical.choose hx)) = Fold (σ ω) :=
    (hσ (Classical.choose hx) ω).1 hchoose
  unfold inducedFoldPermFun
  simp [hx]
  exact htransport

/-- Fiber preservation by `σ` implies the same preservation statement for `σ⁻¹`. -/
lemma fold_equiv_iff_sigma_symm {Ω X : Type} (Fold : Ω → X) (σ : Equiv.Perm Ω)
    (hσ : ∀ ω ω', Fold ω = Fold ω' ↔ Fold (σ ω) = Fold (σ ω')) :
    ∀ ω ω', Fold ω = Fold ω' ↔ Fold (σ.symm ω) = Fold (σ.symm ω') := by
  intro ω ω'
  simpa using (hσ (σ.symm ω) (σ.symm ω')).symm

/-- A fold-compatible source permutation induces a visible permutation on the quotient values; the
fiberwise hidden data are exactly the residual degrees of freedom in the semidirect-product
package.
    thm:op-algebra-fold-equivalence-aut-semidir -/
theorem paper_op_algebra_fold_equivalence_aut_semidir {Ω X : Type} [Fintype Ω] [DecidableEq Ω]
    [Fintype X] [DecidableEq X] (Fold : Ω → X) :
    ∀ σ : Equiv.Perm Ω,
      (∀ ω ω', Fold ω = Fold ω' ↔ Fold (σ ω) = Fold (σ ω')) →
        ∃ ρ : Equiv.Perm X, ∀ ω, Fold (σ ω) = ρ (Fold ω) := by
  classical
  intro σ hσ
  let ρto : X → X := inducedFoldPermFun Fold σ
  let ρinv : X → X := inducedFoldPermFun Fold σ.symm
  have hσsymm : ∀ ω ω', Fold ω = Fold ω' ↔ Fold (σ.symm ω) = Fold (σ.symm ω') :=
    fold_equiv_iff_sigma_symm Fold σ hσ
  have hρto_apply : ∀ ω : Ω, ρto (Fold ω) = Fold (σ ω) := by
    intro ω
    exact inducedFoldPermFun_apply Fold σ hσ ω
  have hρinv_apply : ∀ ω : Ω, ρinv (Fold ω) = Fold (σ.symm ω) := by
    intro ω
    exact inducedFoldPermFun_apply Fold σ.symm hσsymm ω
  have hleft : Function.LeftInverse ρinv ρto := by
    intro x
    by_cases hx : FoldValueReached Fold x
    · rcases hx with ⟨ω, rfl⟩
      rw [hρto_apply ω, hρinv_apply (σ ω)]
      simp
    · have hρto : ρto x = x := by
        simp [ρto, inducedFoldPermFun, hx]
      have hρinv : ρinv x = x := by
        simp [ρinv, inducedFoldPermFun, hx]
      rw [hρto, hρinv]
  have hright : Function.RightInverse ρinv ρto := by
    intro x
    by_cases hx : FoldValueReached Fold x
    · rcases hx with ⟨ω, rfl⟩
      rw [hρinv_apply ω, hρto_apply (σ.symm ω)]
      simp
    · have hρinv : ρinv x = x := by
        simp [ρinv, inducedFoldPermFun, hx]
      have hρto : ρto x = x := by
        simp [ρto, inducedFoldPermFun, hx]
      rw [hρinv, hρto]
  refine ⟨{ toFun := ρto, invFun := ρinv, left_inv := hleft, right_inv := hright }, ?_⟩
  intro ω
  exact (hρto_apply ω).symm

end

end Omega.OperatorAlgebra
