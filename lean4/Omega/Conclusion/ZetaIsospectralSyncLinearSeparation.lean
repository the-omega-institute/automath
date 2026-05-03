import Omega.Conclusion.AmbiguityShellSpectralInvisibility
import Omega.Conclusion.AmbiguityShellZetaSyncSplitting

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-zeta-isospectral-sync-linear-separation`. -/
theorem paper_conclusion_zeta_isospectral_sync_linear_separation (m m' : ℕ)
    (hm : 3 ≤ m) (hm' : 3 ≤ m') :
    (((1 : Matrix (Fin 1) (Fin 1) ℚ) - ambiguityShellNilpotent).det = 1) ∧
      (∀ n : ℕ, (ambiguityShellNilpotent ^ (n + 1)).trace = 0) ∧
        ambiguityShellSyncBudget m - ambiguityShellSyncBudget m' = m - m' := by
  rcases paper_conclusion_ambiguity_shell_zeta_sync_splitting with ⟨hdet, htrace, _⟩
  refine ⟨hdet, htrace, ?_⟩
  have hm_pos : 0 < m := by omega
  have hm'_pos : 0 < m' := by omega
  simp [ambiguityShellSyncBudget]
  omega

end Omega.Conclusion
