import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-kappa-invariant-unification`. -/
theorem paper_xi_kappa_invariant_unification
    (wind blaschkeDegree blaschkeDefect modelDim toeplitzNeg maslov spectralFlow : ℕ)
    (hWB : wind = blaschkeDegree) (hBD : blaschkeDegree = blaschkeDefect)
    (hDM : blaschkeDefect = modelDim) (hMT : modelDim = toeplitzNeg)
    (hTM : toeplitzNeg = maslov) (hMS : maslov = spectralFlow) :
    ∃ κ : ℕ,
      κ = wind ∧ κ = blaschkeDegree ∧ κ = blaschkeDefect ∧ κ = modelDim ∧
        κ = toeplitzNeg ∧ κ = maslov ∧ κ = spectralFlow := by
  refine ⟨wind, rfl, hWB, hWB.trans hBD, hWB.trans (hBD.trans hDM), ?_, ?_, ?_⟩
  · exact hWB.trans (hBD.trans (hDM.trans hMT))
  · exact hWB.trans (hBD.trans (hDM.trans (hMT.trans hTM)))
  · exact hWB.trans (hBD.trans (hDM.trans (hMT.trans (hTM.trans hMS))))

end Omega.Zeta
