import Mathlib.Tactic
import Omega.Conclusion.S4CuspStableLimitNormalizationNodeGenus

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-s4-cusp-stable-contraction-irreducible-nodal-index`. -/
theorem paper_conclusion_s4_cusp_stable_contraction_irreducible_nodal_index
    (delta normalizedGenus : Fin 3 → Nat) (hirr hnonsep : Prop) (hIrr : hirr)
    (hNonsep : hnonsep) (hdelta : delta 0 = 12 ∧ delta 1 = 6 ∧ delta 2 = 4)
    (hgenus : ∀ i, normalizedGenus i + delta i = 16) :
    hirr ∧ hnonsep ∧ delta 0 = 12 ∧ delta 1 = 6 ∧ delta 2 = 4 ∧
      normalizedGenus 0 = 4 ∧ normalizedGenus 1 = 10 ∧ normalizedGenus 2 = 12 := by
  rcases hdelta with ⟨hdelta0, hdelta1, hdelta2⟩
  have hgenus0 : normalizedGenus 0 = 4 := by
    have h := hgenus 0
    rw [hdelta0] at h
    omega
  have hgenus1 : normalizedGenus 1 = 10 := by
    have h := hgenus 1
    rw [hdelta1] at h
    omega
  have hgenus2 : normalizedGenus 2 = 12 := by
    have h := hgenus 2
    rw [hdelta2] at h
    omega
  exact
    ⟨hIrr, hNonsep, hdelta0, hdelta1, hdelta2, hgenus0, hgenus1, hgenus2⟩

end Omega.Conclusion
