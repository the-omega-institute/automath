import Mathlib.Tactic

namespace Omega.Zeta

/-- Two-digit base-`B` evaluation with the low digit first. -/
def xi_time_part9g_canonical_faithful_minimal_radix_threshold_eval
    (B d₀ d₁ : Nat) : Nat :=
  d₀ + B * d₁

/-- Faithfulness of the two-digit evaluation on digits in the interval `0..M`. -/
def xi_time_part9g_canonical_faithful_minimal_radix_threshold_faithful
    (M B : Nat) : Prop :=
  0 < B ∧
    ∀ d₀ d₁ e₀ e₁ : Nat,
      d₀ ≤ M →
        d₁ ≤ M →
          e₀ ≤ M →
            e₁ ≤ M →
              xi_time_part9g_canonical_faithful_minimal_radix_threshold_eval B d₀ d₁ =
                xi_time_part9g_canonical_faithful_minimal_radix_threshold_eval B e₀ e₁ →
                d₀ = e₀ ∧ d₁ = e₁

/-- Paper label: `thm:xi-time-part9g-canonical-faithful-minimal-radix-threshold`. -/
theorem paper_xi_time_part9g_canonical_faithful_minimal_radix_threshold (M B : Nat) :
    xi_time_part9g_canonical_faithful_minimal_radix_threshold_faithful M B ↔ M < B := by
  constructor
  · intro hfaith
    by_contra hnot
    have hle : B ≤ M := Nat.le_of_not_gt hnot
    have hBpos : 0 < B := hfaith.1
    have hOneLe : 1 ≤ M := by omega
    have hcollision :=
      hfaith.2 B 0 0 1 hle (Nat.zero_le M) (Nat.zero_le M) hOneLe
    have heval :
        xi_time_part9g_canonical_faithful_minimal_radix_threshold_eval B B 0 =
          xi_time_part9g_canonical_faithful_minimal_radix_threshold_eval B 0 1 := by
      simp [xi_time_part9g_canonical_faithful_minimal_radix_threshold_eval]
    exact zero_ne_one (hcollision heval).2
  · intro hMB
    refine ⟨by omega, ?_⟩
    intro d₀ d₁ e₀ e₁ hd₀ hd₁ he₀ he₁ heq
    have hd₀B : d₀ < B := by omega
    have he₀B : e₀ < B := by omega
    have hmod :
        (xi_time_part9g_canonical_faithful_minimal_radix_threshold_eval B d₀ d₁) % B =
          (xi_time_part9g_canonical_faithful_minimal_radix_threshold_eval B e₀ e₁) % B :=
      congrArg (fun n : Nat => n % B) heq
    have hd₀_mod :
        (xi_time_part9g_canonical_faithful_minimal_radix_threshold_eval B d₀ d₁) % B = d₀ := by
      rw [xi_time_part9g_canonical_faithful_minimal_radix_threshold_eval,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hd₀B]
    have he₀_mod :
        (xi_time_part9g_canonical_faithful_minimal_radix_threshold_eval B e₀ e₁) % B = e₀ := by
      rw [xi_time_part9g_canonical_faithful_minimal_radix_threshold_eval,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt he₀B]
    have hdigit₀ : d₀ = e₀ := by
      simpa [hd₀_mod, he₀_mod] using hmod
    subst e₀
    have hmul : B * d₁ = B * e₁ := by
      exact Nat.add_left_cancel heq
    have hdigit₁ : d₁ = e₁ := Nat.mul_left_cancel (by omega : 0 < B) hmul
    exact ⟨rfl, hdigit₁⟩

end Omega.Zeta
