import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Omega.Folding.GmFischerCover

namespace Omega.Folding

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the entropy corollary of the folded image shift.
    cor:Phi-m-entropy -/
theorem paper_resolution_folding_phi_m_entropy
    (hTop : ℕ → ℝ)
    (hUpper : ∀ {m : ℕ}, 2 ≤ m → hTop m ≤ Real.log 2)
    (hLower : ∀ {m : ℕ}, 2 ≤ m → Real.log 2 ≤ hTop m) :
    ∀ {m : ℕ}, 2 ≤ m → hTop m = Real.log 2 := by
  intro m hm
  linarith [hUpper hm, hLower hm]

set_option maxHeartbeats 400000 in
/-- Paper-facing entropy wrapper for `Φ_m`: once the right Fischer cover of `Y_m` is identified
with the cover graph `G_m`, any finite-to-one factor realization transports the SFT entropy
formula from the cover to `Y_m`.
    prop:Phi_m-entropy -/
theorem paper_Phi_m_entropy
    (m : ℕ) (hTopYm hTopXAm rhoAm : ℝ)
    (irreducibleShift deterministicRightResolvingPresentation singletonCoreComponent
      followerSeparatedCore labeledIsomorphicToGm rightFischerCoverOfYm
      finiteToOneFactorMap : Prop)
    (hIrreducible : irreducibleShift)
    (hResolve : deterministicRightResolvingPresentation)
    (hCore : deterministicRightResolvingPresentation → singletonCoreComponent)
    (hSeparated : singletonCoreComponent → followerSeparatedCore)
    (hIso : singletonCoreComponent → labeledIsomorphicToGm)
    (hCover : irreducibleShift → deterministicRightResolvingPresentation →
      singletonCoreComponent → followerSeparatedCore → rightFischerCoverOfYm)
    (hFiniteToOne : rightFischerCoverOfYm → finiteToOneFactorMap)
    (hFactorEntropy : finiteToOneFactorMap → hTopYm = hTopXAm)
    (hSFTEntropy : labeledIsomorphicToGm → hTopXAm = Real.log rhoAm) :
    hTopYm = hTopXAm ∧ hTopXAm = Real.log rhoAm ∧ hTopYm = Real.log rhoAm := by
  let _ := m
  rcases paper_resolution_folding_g_m_fischer_cover irreducibleShift
      deterministicRightResolvingPresentation singletonCoreComponent followerSeparatedCore
      labeledIsomorphicToGm rightFischerCoverOfYm hIrreducible hResolve hCore hSeparated hIso
      hCover with ⟨hIsoGm, hFischerCover⟩
  have hCoverEntropy : hTopYm = hTopXAm := hFactorEntropy (hFiniteToOne hFischerCover)
  have hSftEntropy : hTopXAm = Real.log rhoAm := hSFTEntropy hIsoGm
  refine ⟨hCoverEntropy, hSftEntropy, ?_⟩
  calc
    hTopYm = hTopXAm := hCoverEntropy
    _ = Real.log rhoAm := hSftEntropy

/-- Paper label: `prop:Phi_m-entropy`.

The publication theorem is just the transitive closure of the factor entropy equality and
the Perron/Fischer-cover entropy formula. -/
theorem paper_phi_m_entropy (m : Nat) (hTopYm hTopXA logRho : ℝ)
    (h_factor : hTopYm = hTopXA) (h_pf : hTopXA = logRho) : hTopYm = logRho := by
  let _ := m
  exact h_factor.trans h_pf

end Omega.Folding
