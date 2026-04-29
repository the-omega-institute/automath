import Mathlib.Tactic

namespace Omega.POM

/-- Stable-layer distributions in the concrete two-state model. -/
abbrev StableDistribution := Bool → ℝ

/-- Window-layer distributions in the concrete two-bit model. -/
abbrev WindowDistribution := Bool × Bool → ℝ

/-- Lift a stable distribution to the window layer by placing all mass on the diagonal states. -/
def Q_m (π : StableDistribution) : WindowDistribution
  | (false, false) => π false
  | (true, true) => π true
  | _ => 0

/-- Read out the stable layer by forgetting the second coordinate. -/
def P_m (μ : WindowDistribution) : StableDistribution
  | false => μ (false, false) + μ (false, true)
  | true => μ (true, false) + μ (true, true)

/-- The coarse-grained kernel is the lift-evolve-readout composite. -/
def coarseGrainedKernel (K : WindowDistribution → WindowDistribution) :
    StableDistribution → StableDistribution :=
  P_m ∘ K ∘ Q_m

/-- Semantic characterization of a stable-layer kernel as “lift, evolve, then read out”. -/
def SatisfiesCoarseGrainedSemantics
    (K : WindowDistribution → WindowDistribution)
    (Kbar : StableDistribution → StableDistribution) : Prop :=
  ∀ π0, Kbar π0 = P_m (K (Q_m π0))

/-- Paper label: `thm:pom-coarse-grained-kernel`.
In the concrete two-state model, the stable-layer kernel obtained by coarse-graining is precisely
`P_m ∘ K ∘ Q_m`, and this semantic property determines it uniquely. -/
theorem paper_pom_coarse_grained_kernel
    (K : WindowDistribution → WindowDistribution) :
    SatisfiesCoarseGrainedSemantics K (coarseGrainedKernel K) ∧
      ∀ Kbar : StableDistribution → StableDistribution,
        SatisfiesCoarseGrainedSemantics K Kbar → Kbar = coarseGrainedKernel K := by
  refine ⟨?_, ?_⟩
  · intro π0
    rfl
  · intro Kbar hKbar
    funext π0
    exact hKbar π0

end Omega.POM
