import Omega.LogicExpansionChain.WholeChainInvariance

namespace Omega.LogicExpansionChain.WholeChainInvarianceAPAL

open Omega.LogicExpansionChain

set_option maxHeartbeats 400000 in
/-- APAL publication wrapper for finite-chain invariance.
    cor:whole-chain-invariance -/
theorem paper_conservative_extension_whole_chain_invariance_apal
    {Formula : Type} {Model : ℕ → Type} {State : ℕ → Type}
    (forces : ∀ n, Model n → State n → Formula → Prop)
    (forget : ∀ k, Model (k + 1) → Model k)
    (project : ∀ k, (m : Model (k + 1)) → State (k + 1) → State k)
    (hstep : ∀ k (φ : Formula) (m : Model (k + 1)) (p : State (k + 1)),
      forces (k + 1) m p φ ↔ forces k (forget k m) (project k m p) φ) :
    ∀ n (φ : Formula) (m : Model n) (p : State n),
      forces n m p φ ↔
        forces 0 (iterForget forget n m) (iterProject forget project n m p) φ :=
  paper_conservative_extension_whole_chain_invariance_seeds forces forget project hstep

end Omega.LogicExpansionChain.WholeChainInvarianceAPAL
