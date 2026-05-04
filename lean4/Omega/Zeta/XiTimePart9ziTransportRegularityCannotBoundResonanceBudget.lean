import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-time-part9zi-transport-regularity-cannot-bound-resonance-budget`.
Along a subsequence whose transport scale stays in a bounded nonnegative interval, any control
function bounded on bounded intervals would bound the resonance budget, contradicting its
unboundedness on the same subsequence. -/
theorem paper_xi_time_part9zi_transport_regularity_cannot_bound_resonance_budget
    (E T : ℕ → ℝ) (F : ℕ → ℕ)
    (hlog :
      ∃ c : ℝ, 0 < c ∧ ∃ N0 : ℕ, ∀ N ≥ N0, c * Real.log (N : ℝ) ≤ E N)
    (hEunboundedOnF : ∀ B : ℝ, ∃ n : ℕ, B ≤ E (F n))
    (htransport :
      ∃ B : ℝ, ∀ n : ℕ,
        0 ≤ (F n : ℝ) * T (F n) ∧ (F n : ℝ) * T (F n) ≤ B) :
    (∃ c : ℝ, 0 < c ∧ ∃ N0 : ℕ, ∀ N ≥ N0, c * Real.log (N : ℝ) ≤ E N) ∧
      (∀ B : ℝ, ∃ n : ℕ, B ≤ E (F n)) ∧
        ¬ ∃ Φ : ℝ → ℝ,
          (∀ B : ℝ, ∃ M : ℝ, ∀ x : ℝ, 0 ≤ x → x ≤ B → Φ x ≤ M) ∧
            (∀ N : ℕ, E N ≤ Φ ((N : ℝ) * T N)) := by
  refine ⟨hlog, hEunboundedOnF, ?_⟩
  rintro ⟨Φ, hPhiBounded, hcontrols⟩
  rcases htransport with ⟨Btransport, htransportB⟩
  rcases hPhiBounded Btransport with ⟨M, hM⟩
  rcases hEunboundedOnF (M + 1) with ⟨n, hn⟩
  have hx_nonneg : 0 ≤ (F n : ℝ) * T (F n) := (htransportB n).1
  have hx_le : (F n : ℝ) * T (F n) ≤ Btransport := (htransportB n).2
  have hPhi_le : Φ ((F n : ℝ) * T (F n)) ≤ M := hM _ hx_nonneg hx_le
  have hE_le : E (F n) ≤ M := le_trans (hcontrols (F n)) hPhi_le
  linarith

end Omega.Zeta
