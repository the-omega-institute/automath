import Mathlib.Tactic

namespace Omega.OperatorAlgebra

/-- The visible closure idempotent induced by a section-retraction pair. -/
def visibleClosure {M N : Type*} (F : N → M) (Fsharp : M → N) : M → M :=
  F ∘ Fsharp

/-- A channel factors through the Bayes inverse when it is obtained by postcomposing `Fsharp`
with a simulator defined on the visible algebra. -/
def factorsThroughBayesInverse {M N T : Type*} (Fsharp : M → N) (Phi : M → T) : Prop :=
  ∃ S : N → T, Phi = S ∘ Fsharp

/-- Invariance under the visible closure. -/
def fixedByVisibleClosure {M N T : Type*} (F : N → M) (Fsharp : M → N) (Phi : M → T) : Prop :=
  Phi = Phi ∘ visibleClosure F Fsharp

/-- Any simulator in a Bayes-inverse factorization is forced to agree with the restriction of
`Phi` along the visible inclusion `F`. -/
def simulatorUnique {M N T : Type*} (F : N → M) (Fsharp : M → N) (Phi : M → T) : Prop :=
  ∀ ⦃S : N → T⦄, Phi = S ∘ Fsharp → ∀ y, S y = Phi (F y)

/-- Paper label: `thm:op-algebra-bayes-inverse-zk`. For a visible inclusion `F : N → M` with
Bayes inverse `Fsharp : M → N`, factorization through `Fsharp` is equivalent to invariance under
the visible closure `F ∘ Fsharp`, and the simulator is uniquely determined by restricting `Phi`
back to `N`. -/
theorem paper_op_algebra_bayes_inverse_zk
    {M N T : Type*} (F : N → M) (Fsharp : M → N) (Phi : M → T)
    (hsection : Function.LeftInverse Fsharp F) :
    (factorsThroughBayesInverse Fsharp Phi ↔ fixedByVisibleClosure F Fsharp Phi) ∧
      simulatorUnique F Fsharp Phi := by
  refine ⟨?_, ?_⟩
  · constructor
    · rintro ⟨S, rfl⟩
      ext x
      simp [visibleClosure, Function.comp, hsection (Fsharp x)]
    · intro hfixed
      refine ⟨Phi ∘ F, ?_⟩
      ext x
      have hx := congrArg (fun g : M → T => g x) hfixed
      simpa [fixedByVisibleClosure, visibleClosure, Function.comp] using hx
  · intro S hfactor y
    have hy := congrArg (fun g : M → T => g (F y)) hfactor
    simpa [Function.comp, hsection y] using hy.symm

end Omega.OperatorAlgebra
