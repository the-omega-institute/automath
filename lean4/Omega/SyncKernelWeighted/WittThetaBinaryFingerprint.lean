import Mathlib.Tactic
import Omega.SyncKernelWeighted.WittThetaStableResidue

namespace Omega.SyncKernelWeighted

/-- The binary stage residue `B_k^(r)` obtained by reindexing the stable residue theorem at `p = 2`.
-/
def witt_theta_binary_fingerprint_stage (r : ℕ) (A : ℕ → ℤ) (k : ℕ) : ZMod 2 :=
  witt_theta_stable_residue_normalized 2 A (k - r)

/-- The resulting stage-independent binary fingerprint `ε_r`. -/
def witt_theta_binary_fingerprint_epsilon (r : ℕ) (A : ℕ → ℤ) : ZMod 2 :=
  witt_theta_binary_fingerprint_stage r A (r + 1)

/-- Paper label: `cor:witt-theta-binary-fingerprint`.
Specializing the stable-residue theorem to `p = 2` makes the normalized residue class
`B_k^(r)` independent of the stage once `k ≥ r + 1`; the common value is the binary fingerprint
`ε_r`. -/
theorem paper_witt_theta_binary_fingerprint (r : ℕ) (hr : 1 ≤ r) (A : ℕ → ℤ)
    (hscale : wittThetaDerivativeScaling 2 r A) :
    ∀ k, r + 1 ≤ k →
      witt_theta_binary_fingerprint_stage r A k = witt_theta_binary_fingerprint_epsilon r A := by
  have hstable :=
    paper_witt_theta_stable_residue 2 r (by decide : Nat.Prime 2) hr A hscale
  intro k hk
  have hkr : 1 ≤ k - r := by
    omega
  simpa [witt_theta_binary_fingerprint_stage, witt_theta_binary_fingerprint_epsilon] using
    hstable (k - r) hkr

end Omega.SyncKernelWeighted
