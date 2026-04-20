import Mathlib.Tactic
import Omega.CircleDimension.CertificateInverseLimitAddressing

namespace Omega.CircleDimension

/-- Any cofinal nested dyadic certificate chain with shrinking diameter has a unique limit point. -/
theorem paper_cdim_dyadic_cofinal_sparsification {Cert : Type*} (left right : Cert → ℝ)
    (chain : ℕ → Cert)
    (hnested :
      ∀ n,
        Set.Icc (left (chain (n + 1))) (right (chain (n + 1))) ⊆
          Set.Icc (left (chain n)) (right (chain n)))
    (hdiam : ∀ ε > 0, ∃ N, ∀ n ≥ N, right (chain n) - left (chain n) < ε)
    (hclosed : ∀ n, left (chain n) ≤ right (chain n)) :
    ∃! θ : ℝ, ∀ n, θ ∈ Set.Icc (left (chain n)) (right (chain n)) := by
  rcases
      paper_cdim_certificate_inverse_limit_addressing
        (pointsTo := fun _ _ => True)
        (equiv := fun _ _ => True)
        left right chain hnested hdiam hclosed
        (fun _ _ _ _ _ => trivial) with
    ⟨θ, hθ, huniq⟩
  refine ⟨θ, hθ.1, ?_⟩
  intro η hη
  exact huniq η ⟨hη, by intro _ _ _ _; trivial⟩

end Omega.CircleDimension
