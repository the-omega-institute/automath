import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic
import Omega.Conclusion.TwoIncommensurableBasesDestroyVerticalLattice

namespace Omega.Zeta

/-- Paper label: `thm:xi-two-base-deperiodization-no-imag-period`. -/
theorem paper_xi_two_base_deperiodization_no_imag_period {L1 L2 : ℝ} (hL1 : 1 < L1)
    (hL2 : 1 < L2)
    (hirr : ¬ ∃ q : ℚ, Real.log L1 / Real.log L2 = (q : ℝ)) (Period : ℝ → Prop)
    (hforce :
      ∀ T,
        Period T →
          ∃ m n : ℤ,
            T = (2 * Real.pi * (m : ℝ)) / Real.log L1 ∧
              T = (2 * Real.pi * (n : ℝ)) / Real.log L2) :
    ∀ T, Period T → T = 0 := by
  intro T hT
  rcases hforce T hT with ⟨m, n, hm, hn⟩
  by_contra hT_ne
  have hIrr : Irrational (Real.log L1 / Real.log L2) := by
    intro hmem
    rcases hmem with ⟨q, hq⟩
    exact hirr ⟨q, hq.symm⟩
  exact
    (Omega.Conclusion.paper_conclusion_two_incommensurable_bases_destroy_vertical_lattice
      hL1 hL2 hIrr)
      ⟨T, hT_ne, m, n, hm, hn⟩

end Omega.Zeta
