import Omega.Folding.BoundaryLayer
import Omega.Folding.TailPatchIncomplete
import Omega.GU.So10TwoTorsionCentralCollapseNecessity

namespace Omega.GU

open Finset

/-- Chapter-local package for the scale-lift trilemma. The first block records a candidate
tail-patch-local realization at a fixed scale and radius, the second block records a permutation
invariant parity readout together with the nontriviality/register witnesses that the boundary-layer
results rule out, and the third block records the `so(10)` central `2`-torsion data. -/
structure SmScaleLiftTripleObstructionData where
  tailPatchLocality : Prop
  intrinsicChirality : Prop
  so10CentralLift : Prop
  tailPatchScale : Nat
  tailPatchRadius : Nat
  tailPatchWitness :
    ∃ ω : Omega.Word (tailPatchScale + 1),
      tailPatchRadius < (Finset.univ.filter (fun i => Omega.localDefect ω i = true)).card
  tailPatchRealization :
    tailPatchLocality →
      ∃ T : Omega.Word (tailPatchScale + 1) → Omega.Word tailPatchScale,
        (∀ ω, Omega.Fold (T ω) = Omega.X.restrict (Omega.Fold ω)) ∧
        (∀ ω, (Omega.Fold (T ω)).1 = T ω) ∧
        (∀ ω,
          (Finset.univ.filter
            (fun i => Omega.xorWord (Omega.Fold (Omega.truncate ω)).1 (T ω) i = true)).card ≤
              tailPatchRadius)
  boundaryParityReadout : Fin 3 → Fin 2
  intrinsicChiralityPermutationInvariant :
    intrinsicChirality →
      ∀ σ : Equiv.Perm (Fin 3), ∀ x : Fin 3, boundaryParityReadout (σ x) = boundaryParityReadout x
  intrinsicChiralityNontrivial :
    intrinsicChirality → ∃ x y : Fin 3, boundaryParityReadout x ≠ boundaryParityReadout y
  intrinsicChiralityRegisterInjection :
    intrinsicChirality → ∃ f : Fin 3 → Fin 2, Function.Injective f
  so10CollapseData : So10TwoTorsionCentralCollapseData
  so10CentralLiftRetainsThree :
    so10CentralLift → 3 ≤ so10CollapseData.connectedCentralTwoTorsionRank

/-- The scale-lift trilemma is impossible: the tail-patch locality requirement is blocked by the
fold-tail obstruction, the intrinsic-chirality requirement is blocked by the boundary-layer parity
and minimum-register obstructions, and the `so(10)` central-lift requirement is blocked by the
central `2`-torsion collapse theorem.
    thm:sm-scale-lift-triple-obstruction -/
theorem paper_sm_scale_lift_triple_obstruction
    (D : SmScaleLiftTripleObstructionData) :
    Not (And D.tailPatchLocality (And D.intrinsicChirality D.so10CentralLift)) := by
  intro h
  rcases h with ⟨hTail, hChiral, hSo10⟩
  have hTailFalse : False := by
    obtain ⟨T, hCommute, hStable, hTailBound⟩ := D.tailPatchRealization hTail
    exact
      (Omega.Folding.paper_fold_tail_patch_incomplete
        D.tailPatchScale D.tailPatchRadius D.tailPatchWitness) ⟨T, hCommute, hStable, hTailBound⟩
  have hParityFalse : False := by
    have hConst :
        ∀ x y : Fin 3, D.boundaryParityReadout x = D.boundaryParityReadout y :=
      Omega.no_nontrivial_sym_invariant_grading_fin3 D.boundaryParityReadout
        (D.intrinsicChiralityPermutationInvariant hChiral)
    obtain ⟨x, y, hxy⟩ := D.intrinsicChiralityNontrivial hChiral
    exact hxy (hConst x y)
  have hRegisterFalse : False := by
    obtain ⟨f, hf⟩ := D.intrinsicChiralityRegisterInjection hChiral
    exact Omega.three_alternative_needs_two_bits ⟨f, hf⟩
  have hSo10False : False := by
    have hCollapse :=
      paper_so10_2torsion_central_collapse_necessity D.so10CollapseData
    exact hCollapse.1 (D.so10CentralLiftRetainsThree hSo10)
  exact hTailFalse

end Omega.GU
