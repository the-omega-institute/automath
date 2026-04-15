import Omega.Zeta.PhaseCombPoleCounting
import Mathlib.Data.Set.Countable
import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper: `cor:operator-critical-line-paircorr-pure-point`. -/
theorem paper_operator_critical_line_paircorr_pure_point (Δ : ℝ) (B : ℕ) (α : Fin B → ℝ)
    (ΓT : Finset ℝ)
    (hΓ : ∀ γ, γ ∈ ΓT → ∃ b : Fin B, ∃ k : ℤ, γ = α b + k * Δ) :
    ∃ S : Set ℝ, S.Countable ∧
      ∀ d, d ∈ (ΓT.product ΓT).image (fun p => p.1 - p.2) → d ∈ S := by
  classical
  let S : Set ℝ := Set.range fun q : (Fin B × Fin B) × ℤ =>
    α q.1.1 - α q.1.2 + (q.2 : ℝ) * Δ
  refine ⟨S, Set.countable_range _, ?_⟩
  intro d hd
  rcases Finset.mem_image.mp hd with ⟨p, hp, rfl⟩
  rcases Finset.mem_product.mp hp with ⟨hγ, hγ'⟩
  rcases hΓ p.1 hγ with ⟨b, k, hk⟩
  rcases hΓ p.2 hγ' with ⟨b', k', hk'⟩
  refine ⟨((b, b'), k - k'), ?_⟩
  rw [hk, hk']
  norm_num
  ring

end Omega.Zeta
