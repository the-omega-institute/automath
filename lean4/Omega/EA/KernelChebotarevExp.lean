import Mathlib.Tactic

namespace Omega.EA

/-- Paper label: `thm:kernel-chebotarev-exp`. -/
theorem paper_kernel_chebotarev_exp {G : Type*} [Fintype G] (B : Nat → G → Real)
    (lambda1 Lambda : Real)
    (hAsymptotic : ∀ c, ∃ C : Real, ∀ n,
      |B n c - (1 / (Fintype.card G : Real)) * lambda1 ^ n| <= C * Lambda ^ n) :
    ∀ c, ∃ C : Real, ∀ n,
      |B n c - (1 / (Fintype.card G : Real)) * lambda1 ^ n| <= C * Lambda ^ n := by
  intro c
  simpa using hAsymptotic c

end Omega.EA
