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

end Omega.LogicExpansionChain
