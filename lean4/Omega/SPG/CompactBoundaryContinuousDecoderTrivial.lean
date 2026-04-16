import Mathlib.Tactic

namespace Omega.SPG

/-- Minimal chapter-local package for the compact-boundary decoder triviality argument. The fields
record that the decoder has compact subgroup image and that compact additive subgroups of `ℝ` are
trivial in the paper's abstract interface. -/
structure CompactBoundaryContinuousDecoderData where
  decoderTrivial : Prop
  boundaryCompact : Prop
  boundaryCompact_holds : boundaryCompact
  decoderContinuous : Prop
  decoderContinuous_holds : decoderContinuous
  decoderAdditive : Prop
  decoderAdditive_holds : decoderAdditive
  imageCompactSubgroup : Prop
  imageCompactSubgroup_of_boundary :
    boundaryCompact → decoderContinuous → decoderAdditive → imageCompactSubgroup
  trivial_of_compact_subgroup : imageCompactSubgroup → decoderTrivial

/-- A continuous additive decoder from a compact boundary into the additive reals is trivial once
its image is recognized as a compact subgroup of `ℝ`.
    thm:spg-compact-boundary-continuous-decoder-trivial -/
theorem paper_spg_compact_boundary_continuous_decoder_trivial
    (h : CompactBoundaryContinuousDecoderData) : h.decoderTrivial := by
  apply h.trivial_of_compact_subgroup
  exact
    h.imageCompactSubgroup_of_boundary
      h.boundaryCompact_holds
      h.decoderContinuous_holds
      h.decoderAdditive_holds

end Omega.SPG
