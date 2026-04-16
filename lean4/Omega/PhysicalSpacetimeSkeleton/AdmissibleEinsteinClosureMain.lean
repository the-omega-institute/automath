import Omega.PhysicalSpacetimeSkeleton.AdmissibleGlobalEinsteinEquation
import Omega.PhysicalSpacetimeSkeleton.ProceduralGrandChain

namespace Omega.PhysicalSpacetimeSkeleton

universe u

/-- Paper-facing closure theorem packaging the full procedural grand chain together with the
admissible global Einstein equation. -/
theorem paper_physical_spacetime_admissible_einstein_closure_main :
    ∀ (I : Omega.PhysicalSpacetimeSkeleton.InstantiationCriterion.AcceptableInstantiation)
      {ClockC : Type*} [AddGroup ClockC]
      (delta : ClockC → ClockC) (ThetaU dDeltaTau dA OmegaU : ClockC)
      (hTheta : delta ThetaU = dDeltaTau - dA)
      (hDeltaTau : dDeltaTau = 0)
      (hOmega : OmegaU = -dA)
      (hFlat : OmegaU = 0)
      (hExact : delta ThetaU = 0 → ∃ φU : ClockC, delta φU = ThetaU)
      {U : Type} (N : U → Real) (A B : U) (deltaT nuA nuB : Real)
      (hNA : N A != 0) (hNB : N B != 0) (hT : deltaT != 0)
      (hA : nuA = 1 / (N A * deltaT))
      (hB : nuB = 1 / (N B * deltaT))
      (v : Fin 3 → ℝ) (hv : v ≠ 0)
      {ι : Type u} [Fintype ι]
      (F : Omega.PhysicalSpacetimeSkeleton.GlobalLorentzStructure.CompatibleLorentzFamily ι)
      (D : Omega.PhysicalSpacetimeSkeleton.AdmissibleEinsteinClosure) (hAdm : D.admissible),
      ∃ chain : Omega.PhysicalSpacetimeSkeleton.ProceduralGrandChain,
        chain.clockTransport ∧
          chain.localClockPotential ∧
            chain.localRedshift ∧
              chain.auditedSeedRankThree ∧
                chain.auditedSeedQuadraticPositive ∧
                  chain.globalLorentzMetric ∧
                    chain.globalLorentzValue ∧
                      chain.gravitationalEinsteinClosure ∧
                        D.einsteinTensor + D.cosmologicalConstant * D.metric =
                          D.couplingConstant * D.stressEnergy := by
  intro I ClockC _ delta ThetaU dDeltaTau dA OmegaU hTheta hDeltaTau hOmega hFlat hExact U N A B
    deltaT nuA nuB hNA hNB hT hA hB v hv ι _ F D hAdm
  have hAdm' : D.toMinimalSecondOrderCovariantClosure.admissible := hAdm
  obtain ⟨chain, _hInst, hClock, hPotential, hRedshift, hRank, hQuad, hMetric, hValue,
      _hAffine, hEinstein⟩ :=
    paper_physical_spacetime_procedural_grand_chain
      (I := I) (delta := delta) (ThetaU := ThetaU) (dDeltaTau := dDeltaTau) (dA := dA)
      (OmegaU := OmegaU) (hTheta := hTheta) (hDeltaTau := hDeltaTau) (hOmega := hOmega)
      (hFlat := hFlat) (hExact := hExact) (N := N) (A := A) (B := B) (deltaT := deltaT)
      (nuA := nuA) (nuB := nuB) (hNA := hNA) (hNB := hNB) (hT := hT) (hA := hA) (hB := hB)
      (v := v) (hv := hv) (F := F) (G := D.toMinimalSecondOrderCovariantClosure) hAdm'
  have hEquation :
      D.einsteinTensor + D.cosmologicalConstant * D.metric =
        D.couplingConstant * D.stressEnergy :=
    paper_physical_spacetime_admissible_global_einstein_equation D hAdm
  exact ⟨chain, hClock, hPotential, hRedshift, hRank, hQuad, hMetric, hValue, hEinstein,
    hEquation⟩

end Omega.PhysicalSpacetimeSkeleton
