import Omega.Conclusion.Window6Collision
import Omega.GU.Window6AbelianizedParityChargeRootCartanSplitting
import Omega.GU.Window6BdryUpliftResidueStratification
import Omega.GU.Window6ChiralCompressionHypercubeAdjacency
import Omega.GU.Window6ChiralSectorQ4Spectrum
import Omega.GU.ZeckendorfCountClosure
import Omega.SyncKernelWeighted.RealInput40ArityChargeCoboundary

namespace Omega.GU

/-- Paper-facing aggregate of five audited window-`6` conclusion layers: the boundary-uplift/root
dictionary package, the arity-charge finite certificate, the collision-moment finite statistics,
the four-block Smith-spectrum signature, and the `21 + 3` closure certificate. -/
def paper_window6_unified_skeleton_statement : Prop :=
  ((orderOf (34 : ZMod 571) = 285 ∧
      orderOf (144 : ZMod 571) = 285 ∧
      orderOf (55 : ZMod 571) = 19 ∧
      orderOf (89 : ZMod 571) = 570) ∧
    ((b3VisibleSupport.erase zeroWeight).card = 18 ∧
      (c3VisibleSupport.erase zeroWeight).card = 18 ∧
      boundaryZeroWeights.card = 3 ∧
      b3AdjointWeightMultiset.card = 21 ∧
      c3AdjointWeightMultiset.card = 21 ∧
      Fintype.card Window6ShortRootParityBlock = 6 ∧
      Fintype.card Window6LongRootParityBlock = 12 ∧
      Fintype.card Window6BoundaryParityBlock = 3 ∧
      Fintype.card Window6ParityCoordinate = 21 ∧
      Function.LeftInverse window6BoundaryCartanProjection window6BoundaryCartanInclusion ∧
      (∀ boundary,
        window6AbelianizedParityChargeSplit (window6BoundaryCartanInclusion boundary) =
          ((0, 0), boundary)))) ∧
    (∀ D : Omega.SyncKernelWeighted.RealInput40ArityChargeDensityBoundData,
      D.coboundaryNormalization ∧ D.edgeAuditWithPotential ∧ D.primitiveCycleDensityBound ∧
        D.lengthTwoSharpWitness) ∧
    ((8 + 4 + 9 = 21 ∧
        8 * 2 + 4 * 3 + 9 * 4 = 64 ∧
        8 * 4 + 4 * 9 + 9 * 16 = 212) ∧
      212 * 1024 = 53 * 4096) ∧
    (paper_window6_chiral_compression_hypercube_adjacency_stmt 6 ∧
      window6ChiralSectorQ4Spectrum.card = 16 ∧
      window6ChiralSectorQ4SpectrumBinomialForm) ∧
    (Fintype.card (Omega.X 6) + Fintype.card (Omega.X 2) = 24 ∧
      Nat.fib 8 = Fintype.card (Omega.X 6) ∧
      Nat.fib 4 = Fintype.card (Omega.X 2) ∧
      Nat.factorial 4 = 24)

theorem paper_window6_unified_skeleton : paper_window6_unified_skeleton_statement := by
  refine ⟨⟨paper_window6_bdry_uplift_residue_stratification,
      paper_window6_abelianized_parity_charge_root_cartan_splitting⟩, ?_, ?_, ?_,
    paper_su5_count_closure⟩
  · intro D
    have hCoboundary := Omega.SyncKernelWeighted.paper_real_input_40_arity_charge_coboundary D
    have hDensity := Omega.SyncKernelWeighted.paper_real_input_40_arity_charge_density_bound D
    exact ⟨hCoboundary.1, hCoboundary.2.1, hDensity.1, hDensity.2⟩
  · exact ⟨Omega.Conclusion.window6_qmoment_triple, Omega.Conclusion.paper_window6_collision_prob⟩
  · refine ⟨paper_window6_chiral_compression_hypercube_adjacency 6 (by omega), ?_, ?_⟩
    · native_decide
    · change
        window6ChiralSectorQ4Spectrum =
          Multiset.replicate (Nat.choose 4 0) 4 +
            Multiset.replicate (Nat.choose 4 1) 2 +
            Multiset.replicate (Nat.choose 4 2) 0 +
            Multiset.replicate (Nat.choose 4 3) (-2) +
            Multiset.replicate (Nat.choose 4 4) (-4)
      native_decide

end Omega.GU
