import Mathlib.Tactic
import Omega.Zeta.KilloSmithLossSpectrum

namespace Omega.Zeta

lemma smithDelta_antitone_succ (s : Multiset ℕ) (k : ℕ) :
    Omega.Zeta.smithDelta s (k + 2) ≤ Omega.Zeta.smithDelta s (k + 1) := by
  unfold Omega.Zeta.smithDelta
  exact Multiset.card_le_card <|
    Multiset.monotone_filter_right s (by
      intro v hv
      omega)

/-- Paper label: `thm:xi-smith-loss-discrete-curvature-atoms`. -/
theorem paper_xi_smith_loss_discrete_curvature_atoms (s : Multiset ℕ) :
    (∀ k : ℕ,
      Omega.Zeta.smithEntropy s (k + 2) + Omega.Zeta.smithEntropy s k ≤
        2 * Omega.Zeta.smithEntropy s (k + 1)) ∧
      ∀ k : ℕ,
        (s.filter fun v => v = k + 1).card =
          (Omega.Zeta.smithEntropy s (k + 1) - Omega.Zeta.smithEntropy s k) -
            (Omega.Zeta.smithEntropy s (k + 2) - Omega.Zeta.smithEntropy s (k + 1)) := by
  refine ⟨?_, ?_⟩
  · intro k
    calc
      Omega.Zeta.smithEntropy s (k + 2) + Omega.Zeta.smithEntropy s k =
          (Omega.Zeta.smithEntropy s (k + 1) + Omega.Zeta.smithDelta s (k + 2)) +
            Omega.Zeta.smithEntropy s k := by
              rw [Omega.Zeta.smithEntropy_succ_eq_add_delta s (k + 1)]
      _ ≤ (Omega.Zeta.smithEntropy s (k + 1) + Omega.Zeta.smithDelta s (k + 1)) +
            Omega.Zeta.smithEntropy s k := by
              exact Nat.add_le_add_right
                (Nat.add_le_add_left (smithDelta_antitone_succ s k)
                  (Omega.Zeta.smithEntropy s (k + 1)))
                (Omega.Zeta.smithEntropy s k)
      _ = Omega.Zeta.smithEntropy s (k + 1) + Omega.Zeta.smithEntropy s (k + 1) := by
              rw [Omega.Zeta.smithEntropy_succ_eq_add_delta s k]
              ac_rfl
      _ = 2 * Omega.Zeta.smithEntropy s (k + 1) := by
              rw [two_mul]
  · intro k
    calc
      (s.filter fun v => v = k + 1).card =
          Omega.Zeta.smithDelta s (k + 1) - Omega.Zeta.smithDelta s (k + 2) := by
            exact Omega.Zeta.smithMultiplicity_eq_delta_sub s (k + 1)
      _ = (Omega.Zeta.smithEntropy s (k + 1) - Omega.Zeta.smithEntropy s k) -
            (Omega.Zeta.smithEntropy s (k + 2) - Omega.Zeta.smithEntropy s (k + 1)) := by
            have hΔ1 :
                Omega.Zeta.smithEntropy s (k + 1) - Omega.Zeta.smithEntropy s k =
                  Omega.Zeta.smithDelta s (k + 1) := by
              rw [Omega.Zeta.smithEntropy_succ_eq_add_delta s k]
              simpa using Nat.add_sub_cancel_left (Omega.Zeta.smithEntropy s k)
                (Omega.Zeta.smithDelta s (k + 1))
            have hΔ2 :
                Omega.Zeta.smithEntropy s (k + 2) - Omega.Zeta.smithEntropy s (k + 1) =
                  Omega.Zeta.smithDelta s (k + 2) := by
              rw [Omega.Zeta.smithEntropy_succ_eq_add_delta s (k + 1)]
              simpa using Nat.add_sub_cancel_left (Omega.Zeta.smithEntropy s (k + 1))
                (Omega.Zeta.smithDelta s (k + 2))
            rw [hΔ1, hΔ2]

end Omega.Zeta
