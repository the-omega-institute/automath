import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part75-resonance-anomaly-rigid-core-infinite-tail`. -/
theorem paper_xi_time_part75_resonance_anomaly_rigid_core_infinite_tail
    (Gamma C : ℕ → ℝ)
    (hFiniteLower :
      ∀ U : ℕ, ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
        1 + 2 * ((Finset.range U).sum (fun u => C u ^ 2)) ≤ Gamma m)
    (hTailDiverges :
      ∀ B : ℝ, ∃ U : ℕ,
        B ≤ 1 + 2 * ((Finset.range U).sum (fun u => C u ^ 2))) :
    ∀ B : ℝ, ∃ M : ℕ, ∀ m : ℕ, M ≤ m → B ≤ Gamma m := by
  intro B
  rcases hTailDiverges B with ⟨U, hU⟩
  rcases hFiniteLower U with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  intro m hm
  exact le_trans hU (hM m hm)

end Omega.Zeta
