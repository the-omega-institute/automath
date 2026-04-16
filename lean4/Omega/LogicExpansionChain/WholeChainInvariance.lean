import Mathlib.Tactic

namespace Omega.LogicExpansionChain

/-- Compose the forgetful maps from level `n` down to level `0`. -/
def iterForget {Model : ℕ → Type*} (forget : ∀ k, Model (k + 1) → Model k) :
    ∀ n, Model n → Model 0
  | 0, m => m
  | n + 1, m => iterForget forget n (forget n m)

/-- Compose the state projections from level `n` down to level `0`. -/
def iterProject {Model : ℕ → Type*} {State : ℕ → Type*}
    (forget : ∀ k, Model (k + 1) → Model k)
    (project : ∀ k, (m : Model (k + 1)) → State (k + 1) → State k) :
    ∀ n, (m : Model n) → State n → State 0
  | 0, _, p => p
  | n + 1, m, p => iterProject forget project n (forget n m) (project n m p)

set_option maxHeartbeats 400000 in
/-- Paper-facing seed: a finite chain of conservative extensions preserves forcing after
projecting back to the bottom layer.
    cor:whole-chain-invariance -/
theorem paper_conservative_extension_whole_chain_invariance_seeds
    {Formula : Type} {Model : ℕ → Type} {State : ℕ → Type}
    (forces : ∀ n, Model n → State n → Formula → Prop)
    (forget : ∀ k, Model (k + 1) → Model k)
    (project : ∀ k, (m : Model (k + 1)) → State (k + 1) → State k)
    (hstep : ∀ k (φ : Formula) (m : Model (k + 1)) (p : State (k + 1)),
      forces (k + 1) m p φ ↔ forces k (forget k m) (project k m p) φ) :
    ∀ n (φ : Formula) (m : Model n) (p : State n),
      forces n m p φ ↔
        forces 0 (iterForget forget n m) (iterProject forget project n m p) φ := by
  intro n
  induction n with
  | zero =>
      intro φ m p
      rfl
  | succ k ih =>
      intro φ m p
      exact (hstep k φ m p).trans (ih φ (forget k m) (project k m p))

set_option maxHeartbeats 400000 in
/-- Paper-facing specialization of finite-chain invariance to a single forgetful projection from a
fiberized spacetime state back to its underlying forcing state.
    prop:logic-expansion-spacetime-fiberization-conservative -/
theorem paper_logic_expansion_spacetime_fiberization_conservative
    {Formula BaseModel FiberModel BaseState FiberState : Type}
    (forcesBase : BaseModel → BaseState → Formula → Prop)
    (forcesFiber : FiberModel → FiberState → Formula → Prop)
    (forget : FiberModel → BaseModel)
    (project : FiberModel → FiberState → BaseState)
    (hstep : ∀ (φ : Formula) (m : FiberModel) (p : FiberState),
      forcesFiber m p φ ↔ forcesBase (forget m) (project m p) φ) :
    ∀ (φ : Formula) (m : FiberModel) (p : FiberState),
      forcesFiber m p φ ↔ forcesBase (forget m) (project m p) φ := by
  intro φ m p
  let Model : ℕ → Type := fun
    | 0 => BaseModel
    | _ + 1 => FiberModel
  let State : ℕ → Type := fun
    | 0 => BaseState
    | _ + 1 => FiberState
  let forces : ∀ n, Model n → State n → Formula → Prop := fun
    | 0 => forcesBase
    | _ + 1 => forcesFiber
  let forgetChain : ∀ k, Model (k + 1) → Model k := fun
    | 0 => forget
    | _ + 1 => id
  let projectChain : ∀ k, (x : Model (k + 1)) → State (k + 1) → State k := fun
    | 0 => project
    | _ + 1 => fun _ s => s
  have hchain : ∀ k (ψ : Formula) (x : Model (k + 1)) (s : State (k + 1)),
      forces (k + 1) x s ψ ↔
        forces k (forgetChain k x) (projectChain k x s) ψ := by
    intro k ψ x s
    cases k with
    | zero =>
        simpa [forces, forgetChain, projectChain] using hstep ψ x s
    | succ k =>
        simp [forces, forgetChain, projectChain]
  simpa [Model, State, forces, forgetChain, projectChain, iterForget, iterProject] using
    (paper_conservative_extension_whole_chain_invariance_seeds
      forces forgetChain projectChain hchain 1 φ m p)

end Omega.LogicExpansionChain
