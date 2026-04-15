import Omega.PhysicalSpacetimeSkeleton.AuditedSeedRankThree
import Omega.PhysicalSpacetimeSkeleton.ClockTransportEquation
import Omega.PhysicalSpacetimeSkeleton.GlobalLorentzStructure
import Omega.PhysicalSpacetimeSkeleton.GravitationalScalarUniqueness
import Omega.PhysicalSpacetimeSkeleton.InstantiationCriterion
import Omega.PhysicalSpacetimeSkeleton.LocalClockPotential
import Omega.PhysicalSpacetimeSkeleton.LocalRedshift

namespace Omega.PhysicalSpacetimeSkeleton

universe u

/-- Chapter-local package collecting the ten paper-facing outputs used in the procedural grand
chain: instantiation, transport, local potential, local redshift, audited seed rank/positivity,
global Lorentz gluing/value, and affine/Einstein gravitational closure. -/
structure ProceduralGrandChain where
  instantiation : Prop
  clockTransport : Prop
  localClockPotential : Prop
  localRedshift : Prop
  auditedSeedRankThree : Prop
  auditedSeedQuadraticPositive : Prop
  globalLorentzMetric : Prop
  globalLorentzValue : Prop
  gravitationalAffineClosure : Prop
  gravitationalEinsteinClosure : Prop

/-- Paper-facing procedural grand chain: the chapter-local package is assembled by gluing the
already formalized wrappers for instantiation, clock transport, local clock potential, local
redshift, audited seeds, global Lorentz structure, and gravitational scalar uniqueness.
    thm:physical-spacetime-procedural-grand-chain -/
theorem paper_physical_spacetime_procedural_grand_chain :
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
      (G : MinimalSecondOrderCovariantClosure) (hAdm : G.admissible),
      ∃ chain : ProceduralGrandChain,
        chain.instantiation ∧
        chain.clockTransport ∧
        chain.localClockPotential ∧
        chain.localRedshift ∧
        chain.auditedSeedRankThree ∧
        chain.auditedSeedQuadraticPositive ∧
        chain.globalLorentzMetric ∧
        chain.globalLorentzValue ∧
        chain.gravitationalAffineClosure ∧
        chain.gravitationalEinsteinClosure := by
  intro I ClockC _ delta ThetaU dDeltaTau dA OmegaU hTheta hDeltaTau hOmega hFlat hExact
    U N A B deltaT nuA nuB hNA hNB hT hA hB v hv ι _ F G hAdm
  have hInst :
      Omega.PhysicalSpacetimeSkeleton.InstantiationCriterion.InstantiatesPhysicalSpacetime I :=
    Omega.PhysicalSpacetimeSkeleton.InstantiationCriterion.paper_physical_spacetime_instantiation_criterion I
  have hClock : delta ThetaU = OmegaU :=
    paper_physical_spacetime_clock_transport_equation delta ThetaU dDeltaTau dA OmegaU
      hTheta hDeltaTau hOmega
  have hPotential : ∃ φU : ClockC, ThetaU = delta φU :=
    paper_physical_spacetime_local_clock_potential delta ThetaU dDeltaTau dA OmegaU
      hTheta hDeltaTau hOmega hFlat hExact
  have hRedshift : nuB / nuA = N A / N B :=
    paper_physical_spacetime_local_redshift N A B deltaT nuA nuB hNA hNB hT hA hB
  have hRank :
      Omega.PhysicalSpacetimeSkeleton.AuditedSeedRankThree.auditedSeedMatrix.rank = 3 :=
    Omega.PhysicalSpacetimeSkeleton.AuditedSeedRankThree.paper_physical_spacetime_audited_seed_rank_three
  have hQuad :
      0 <
        dotProduct v
          ((Omega.PhysicalSpacetimeSkeleton.AuditedSeedRankThree.auditedSeedMatrix.transpose *
              Omega.PhysicalSpacetimeSkeleton.AuditedSeedRankThree.auditedSeedMatrix).mulVec v) :=
    Omega.PhysicalSpacetimeSkeleton.AuditedSeedRankThree.paper_physical_spacetime_audited_seed_local_space_quadratic_positive
      v hv
  obtain ⟨g, hg, hLorentz⟩ :=
    Omega.PhysicalSpacetimeSkeleton.GlobalLorentzStructure.paper_physical_spacetime_global_lorentz_structure
      F
  obtain ⟨ga, gb, divergence, hAffine, hga, hgb, hEinstein⟩ :=
    paper_physical_spacetime_gravitational_scalar_uniqueness G hAdm
  refine
    ⟨{ instantiation :=
         Omega.PhysicalSpacetimeSkeleton.InstantiationCriterion.InstantiatesPhysicalSpacetime I
       clockTransport := delta ThetaU = OmegaU
       localClockPotential := ∃ φU : ClockC, ThetaU = delta φU
       localRedshift := nuB / nuA = N A / N B
       auditedSeedRankThree :=
         Omega.PhysicalSpacetimeSkeleton.AuditedSeedRankThree.auditedSeedMatrix.rank = 3
       auditedSeedQuadraticPositive :=
         0 <
           dotProduct v
             ((Omega.PhysicalSpacetimeSkeleton.AuditedSeedRankThree.auditedSeedMatrix.transpose *
                 Omega.PhysicalSpacetimeSkeleton.AuditedSeedRankThree.auditedSeedMatrix).mulVec v)
       globalLorentzMetric :=
         ∃ g :
             Omega.PhysicalSpacetimeSkeleton.GlobalLorentzStructure.maximalAdmissibleDomain F →
               ℝ,
           ∀ i x,
             g
                 (Omega.PhysicalSpacetimeSkeleton.GlobalLorentzStructure.pointClass F i x) =
               F.metric i x
       globalLorentzValue :=
         ∃ g :
             Omega.PhysicalSpacetimeSkeleton.GlobalLorentzStructure.maximalAdmissibleDomain F →
               ℝ,
           ∀ q,
             Omega.PhysicalSpacetimeSkeleton.GlobalLorentzStructure.IsLorentzValue (g q)
       gravitationalAffineClosure :=
         ∃ a b divergence : ℝ, G.gravitationalScalar = a * G.ricciScalar + b + divergence
       gravitationalEinsteinClosure :=
         ∃ a b : ℝ,
           a = 1 ∧
             b = -2 * G.cosmologicalConstant ∧
               a * G.ricciScalar + b = G.ricciScalar - 2 * G.cosmologicalConstant }, ?_⟩
  refine ⟨hInst, hClock, hPotential, hRedshift, hRank, hQuad, ?_, ?_, ?_, ?_⟩
  · exact ⟨g, hg⟩
  · exact ⟨g, hLorentz⟩
  · exact ⟨ga, gb, divergence, hAffine⟩
  · exact ⟨ga, gb, hga, hgb, hEinstein⟩

/-- Once the backend preserves the chapter interface, the quantum and spacetime outputs are
structural consequences and require no extra axioms.
    cor:physical-spacetime-no-new-axioms -/
theorem paper_physical_spacetime_no_new_axioms
    (backendPreservesInterface quantumStructure spacetimeStructure : Prop)
    (hQuantum : backendPreservesInterface → quantumStructure)
    (hSpacetime : backendPreservesInterface → spacetimeStructure) :
    backendPreservesInterface → quantumStructure ∧ spacetimeStructure := by
  intro hBackend
  exact ⟨hQuantum hBackend, hSpacetime hBackend⟩

end Omega.PhysicalSpacetimeSkeleton
