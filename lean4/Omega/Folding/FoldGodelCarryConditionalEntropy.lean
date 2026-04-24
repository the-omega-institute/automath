import Omega.Folding.FiberGaugeVolumeIncrementConditionalShannonStirling

namespace Omega.Folding

/-- The normalized conditional-entropy main term used for the Godel carry wrapper. -/
noncomputable abbrev foldGodelCarryConditionalEntropyMainTerm
    {Omega X Y : Type*} [Fintype Omega] [Fintype X] [Fintype Y]
    (f : Omega → X) (pi : X → Y) : ℝ :=
  fiberGaugeConditionalShannon f pi

/-- The explicit Stirling correction term used for the Godel carry wrapper. -/
noncomputable abbrev foldGodelCarryConditionalEntropyCorrection
    {Omega X Y : Type*} [Fintype Omega] [Fintype X] [Fintype Y]
    (f : Omega → X) (pi : X → Y) : ℝ :=
  fiberGaugeStirlingCorrection f pi

/-- Concrete Godel-carry conditional-entropy statement: the normalized log-gauge increment equals
the conditional Shannon term plus the explicit Stirling correction up to the standard
second-order remainder. -/
abbrev FoldGodelCarryConditionalEntropyStatement
    {Omega X Y : Type*} [Fintype Omega] [Fintype X] [Fintype Y]
    (f : Omega → X) (pi : X → Y) : Prop :=
  fiberGaugeVolumeIncrementConditionalShannonStirling f pi

/-- Paper label: `thm:fold-godel-carry-conditional-entropy`. -/
theorem paper_fold_godel_carry_conditional_entropy
    {Omega X Y : Type*} [Fintype Omega] [Fintype X] [Fintype Y]
    (f : Omega → X) (pi : X → Y) (hf : Function.Surjective f) (hpi : Function.Surjective pi) :
    FoldGodelCarryConditionalEntropyStatement f pi := by
  simpa [FoldGodelCarryConditionalEntropyStatement,
    foldGodelCarryConditionalEntropyMainTerm, foldGodelCarryConditionalEntropyCorrection] using
    paper_fiber_gauge_volume_increment_conditional_shannon_stirling f pi hf hpi

end Omega.Folding
