import Mathlib.Tactic

namespace Omega.CircleDimension

/-- The product mediator obtained from the solenoid-side mediator `f` and the residue-axis
mediator `g`. -/
def solenoidResidueProductMediator
    {Sigma SigmaS P Zhat : Type*} (f : Sigma → SigmaS) (g : P → Zhat) :
    Sigma × P → SigmaS × Zhat
  | (x, p) => (f x, g p)

/-- The product mediator is unique when both component terminal mediators are unique. -/
def uniqueProductMediator
    {Sigma SigmaS P Zhat T R : Type*}
    (π : Sigma → T) (πS : SigmaS → T)
    (ψ : ℕ → P → R) (πn : ℕ → Zhat → R)
    (f : Sigma → SigmaS) (g : P → Zhat) : Prop :=
  let F := solenoidResidueProductMediator f g
  (∀ z, πS (F z).1 = π z.1) ∧
    (∀ n z, πn n (F z).2 = ψ n z.2) ∧
    ∀ G : Sigma × P → SigmaS × Zhat,
      (∀ z, πS (G z).1 = π z.1) →
      (∀ n z, πn n (G z).2 = ψ n z.2) →
      G = F

/-- Paper label: `thm:cdim-solenoid-residue-double-terminal-synthesis`.

Once the solenoid-side mediator `f` and the residue-axis mediator `g` are unique on their own
terminal problems, the product map `F = f × g` is the unique mediator for the product problem. -/
theorem paper_cdim_solenoid_residue_double_terminal_synthesis
    {Sigma SigmaS P Zhat T R : Type*}
    (π : Sigma → T) (πS : SigmaS → T)
    (ψ : ℕ → P → R) (πn : ℕ → Zhat → R)
    (f : Sigma → SigmaS) (g : P → Zhat)
    (hf_comm : ∀ x, πS (f x) = π x)
    (hg_comm : ∀ n p, πn n (g p) = ψ n p)
    (hf_unique : ∀ f' : Sigma → SigmaS, (∀ x, πS (f' x) = π x) → f' = f)
    (hg_unique : ∀ g' : P → Zhat, (∀ n p, πn n (g' p) = ψ n p) → g' = g) :
    uniqueProductMediator π πS ψ πn f g := by
  dsimp [uniqueProductMediator]
  refine ⟨?_, ?_, ?_⟩
  · intro z
    rcases z with ⟨x, p⟩
    simp [solenoidResidueProductMediator, hf_comm]
  · intro n z
    rcases z with ⟨x, p⟩
    simp [solenoidResidueProductMediator, hg_comm]
  · intro G hG₁ hG₂
    funext z
    rcases z with ⟨x, p⟩
    have hfst : (G (x, p)).1 = f x := by
      let f' : Sigma → SigmaS := fun x' => (G (x', p)).1
      have hf' : ∀ x', πS (f' x') = π x' := by
        intro x'
        simpa [f'] using hG₁ (x', p)
      have hff' : f' = f := hf_unique f' hf'
      exact congrArg (fun h : Sigma → SigmaS => h x) hff'
    have hsnd : (G (x, p)).2 = g p := by
      let g' : P → Zhat := fun p' => (G (x, p')).2
      have hg' : ∀ n p', πn n (g' p') = ψ n p' := by
        intro n p'
        simpa [g'] using hG₂ n (x, p')
      have hgg' : g' = g := hg_unique g' hg'
      exact congrArg (fun h : P → Zhat => h p) hgg'
    ext <;> simp [solenoidResidueProductMediator, hfst, hsnd]

end Omega.CircleDimension
