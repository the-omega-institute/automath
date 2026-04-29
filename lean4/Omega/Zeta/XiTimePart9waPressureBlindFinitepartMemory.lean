import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-time-part9wa-pressure-blind-finitepart-memory`. -/
theorem paper_xi_time_part9wa_pressure_blind_finitepart_memory
    (P Pcore logM logMcore atom : ℝ → ℝ) (u θ : ℝ)
    (hP : ∀ θ, P θ = Pcore θ)
    (hM : ∀ u, logM u = logMcore u + atom u)
    (hatom : 0 < atom u) :
    P θ = Pcore θ ∧ logM u - logMcore u = atom u ∧
      0 < logM u - logMcore u := by
  have hdiff : logM u - logMcore u = atom u := by
    rw [hM u]
    ring
  exact ⟨hP θ, hdiff, by simpa [hdiff] using hatom⟩

end Omega.Zeta
