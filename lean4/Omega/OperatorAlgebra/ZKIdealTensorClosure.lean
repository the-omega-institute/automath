import Mathlib.Tactic
import Omega.OperatorAlgebra.BayesInverseZK

namespace Omega.OperatorAlgebra

/-- Product-tensor of two channel maps, modeled on cartesian products. -/
def tensorChannel {M M' T T' : Type*} (Phi : M → T) (Phi' : M' → T') : M × M' → T × T' :=
  fun x => (Phi x.1, Phi' x.2)

/-- Paper label: `cor:op-algebra-zk-ideal-tensor-closure`. The fixed-point description of the
zero-knowledge class is closed under postcomposition, affine combinations, and product tensors. -/
theorem paper_op_algebra_zk_ideal_tensor_closure
    {M N T T' M' N' U : Type*} [AddCommMonoid T] [Module ℝ T]
    (F : N → M) (Fsharp : M → N) (F' : N' → M') (Fsharp' : M' → N') :
    (∀ {Phi : M → T} {Psi : T → T'},
      fixedByVisibleClosure F Fsharp Phi →
        fixedByVisibleClosure F Fsharp (Psi ∘ Phi)) ∧
      (∀ {Phi₁ Phi₂ : M → T} {p : ℝ},
        fixedByVisibleClosure F Fsharp Phi₁ →
        fixedByVisibleClosure F Fsharp Phi₂ →
        fixedByVisibleClosure F Fsharp (fun x => p • Phi₁ x + (1 - p) • Phi₂ x)) ∧
      (∀ {Phi : M → T} {Phi' : M' → U},
        fixedByVisibleClosure F Fsharp Phi →
        fixedByVisibleClosure F' Fsharp' Phi' →
        fixedByVisibleClosure (Prod.map F F') (Prod.map Fsharp Fsharp')
          (tensorChannel Phi Phi')) := by
  refine ⟨?_, ?_, ?_⟩
  · intro Phi Psi hPhi
    ext x
    have hx := congrArg (fun g : M → T => g x) hPhi
    simpa [fixedByVisibleClosure, visibleClosure, Function.comp] using congrArg Psi hx
  · intro Phi₁ Phi₂ p hPhi₁ hPhi₂
    ext x
    have hx₁ :
        Phi₁ (visibleClosure F Fsharp x) = Phi₁ x := by
      simpa [fixedByVisibleClosure, visibleClosure, Function.comp] using
        (congrArg (fun g : M → T => g x) hPhi₁).symm
    have hx₂ :
        Phi₂ (visibleClosure F Fsharp x) = Phi₂ x := by
      simpa [fixedByVisibleClosure, visibleClosure, Function.comp] using
        (congrArg (fun g : M → T => g x) hPhi₂).symm
    simp [Function.comp, hx₁, hx₂]
  · intro Phi Phi' hPhi hPhi'
    funext x
    rcases x with ⟨m, m'⟩
    exact Prod.ext
      (by
        simpa [fixedByVisibleClosure, visibleClosure, tensorChannel, Function.comp] using
          congrArg (fun g : M → T => g m) hPhi)
      (by
        simpa [fixedByVisibleClosure, visibleClosure, tensorChannel, Function.comp] using
          congrArg (fun g : M' → U => g m') hPhi')

end Omega.OperatorAlgebra
