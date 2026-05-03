import Mathlib.Tactic

namespace Omega.POM.AnomCyclotomicPhaseTorsion

/-- Paper label: `cor:pom-anom-cyclotomic-phase-torsion`. -/
theorem paper_pom_anom_cyclotomic_phase_torsion {H : Type _} [AddCommMonoid H] (a : H)
    (N : ℕ) (hN : 0 < N) (hkill : N • a = 0) : ∃ q : ℕ, 2 ≤ q ∧ q • a = 0 := by
  refine ⟨2 * N, ?_, ?_⟩
  · omega
  · have htwo : 2 * N = N + N := by omega
    rw [htwo, add_nsmul, hkill]
    simp

end Omega.POM.AnomCyclotomicPhaseTorsion
