import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-natural-extension-infinite-prime-register-necessity`. -/
theorem paper_xi_natural_extension_infinite_prime_register_necessity
    (ExactWithSlices : ℕ → Prop) (RecoversDepth : ℕ → ℕ → Prop)
    (finite_to_depth : ∀ k N, ExactWithSlices k → RecoversDepth k N)
    (depth_lower_bound : ∀ k N, k < N → ¬ RecoversDepth k N) :
    ¬ ∃ k, ExactWithSlices k := by
  rintro ⟨k, hk⟩
  exact depth_lower_bound k (k + 1) (Nat.lt_succ_self k) (finite_to_depth k (k + 1) hk)

end Omega.Zeta
