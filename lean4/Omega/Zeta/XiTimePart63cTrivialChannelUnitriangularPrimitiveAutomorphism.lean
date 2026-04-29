import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part63c-trivial-channel-unitriangular-primitive-automorphism`. -/
theorem paper_xi_time_part63c_trivial_channel_unitriangular_primitive_automorphism
    (Q : ℕ) (T b : ℕ → ℤ) (P : ℕ → (ℕ → ℤ) → ℤ)
    (hT : ∀ q, 1 ≤ q → q ≤ Q → T q = b q + P q b)
    (hP_local : ∀ q x y, (∀ i, i < q → x i = y i) → P q x = P q y) :
    ∃ inv : ℕ → ℤ,
      (∀ q, 1 ≤ q → q ≤ Q → inv q = T q - P q inv) ∧
        (∀ q, 1 ≤ q → q ≤ Q → inv q = b q) := by
  have _ : P 0 b = P 0 b := hP_local 0 b b (by intro i hi; rfl)
  refine ⟨b, ?_, ?_⟩
  · intro q hq1 hqQ
    have h := hT q hq1 hqQ
    omega
  · intro q hq1 hqQ
    rfl

end Omega.Zeta
