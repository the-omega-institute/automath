import Omega.Zeta.XiFoldCongruenceUnitalAutomorphismRigidity

namespace Omega.Discussion

/-- The discussion quotient semiring inherits the automorphism rigidity of the concrete
fold-congruence model.
    prop:discussion-window-quotient-semiring-rigidity -/
theorem paper_discussion_window_quotient_semiring_rigidity (m : ℕ) :
    ∀ σ : Omega.Zeta.foldCongruenceSemiring m ≃+* Omega.Zeta.foldCongruenceSemiring m,
      σ = RingEquiv.refl _ := by
  intro σ
  exact Omega.Zeta.foldCongruence_ringEquiv_eq_refl m σ

end Omega.Discussion
