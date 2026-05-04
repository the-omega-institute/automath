import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-s4-cusp-lmhs-weight-jacobian-semiabelian`. -/
theorem paper_conclusion_s4_cusp_lmhs_weight_jacobian_semiabelian
    (delta normalizedGenus gr0 gr1 gr2 torusRank abelianDim : Fin 3 → ℕ)
    (hdelta : delta 0 = 12 ∧ delta 1 = 6 ∧ delta 2 = 4)
    (hgenus : ∀ i, normalizedGenus i + delta i = 16)
    (hgr0 : ∀ i, gr0 i = delta i)
    (hgr1 : ∀ i, gr1 i = 2 * normalizedGenus i)
    (hgr2 : ∀ i, gr2 i = delta i)
    (htorus : ∀ i, torusRank i = delta i)
    (habelian : ∀ i, abelianDim i = normalizedGenus i) :
    (∀ i,
        gr0 i = delta i ∧ gr1 i = 2 * normalizedGenus i ∧ gr2 i = delta i ∧
          torusRank i = delta i ∧ abelianDim i = normalizedGenus i) ∧
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
  refine ⟨?_, hgenus0, hgenus1, hgenus2⟩
  intro i
  exact ⟨hgr0 i, hgr1 i, hgr2 i, htorus i, habelian i⟩
