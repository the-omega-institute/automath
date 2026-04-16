import Mathlib.Tactic

namespace Omega.TypedAddressBiaxialCompletion

universe u

/-- Minimal observer-spacetime interface used by the typed-address instantiation wrapper. -/
structure ObserverSpacetimeInterface (State : Type u) where
  timeProjection : State → ℝ

/-- Minimal causal-compatibility interface providing the extracted reachability preorder. -/
structure CausalCompatibilityInterface (State : Type u) where
  causalPreorder : State → State → Prop

/-- Minimal resource interface providing the scalarized resource quasidistance. -/
structure ResourceQuasidistanceInterface (State : Type u) where
  resourceQuasidistance : State → State → ℝ

/-- Minimal obstruction interface packaging the residual obstruction readout. -/
structure ObstructionInterface (State : Type u) where
  obstruction : State → State → Prop

/-- Chapter-local admissible instantiation package for the rough spacetime extraction wrapper. -/
structure AdmissiblePhysicalInstantiation where
  State : Type u
  observerSpacetime : ObserverSpacetimeInterface State
  causalCompatibility : CausalCompatibilityInterface State
  resourceQuasidistance : ResourceQuasidistanceInterface State
  obstructionInterface : ObstructionInterface State

/-- The extracted rough spacetime quadruple `(≼, τ, d_res, Ω)`. -/
structure RoughSpacetimeQuadruple (State : Type u) where
  causalPreorder : State → State → Prop
  timeProjection : State → ℝ
  resourceQuasidistance : State → State → ℝ
  obstruction : State → State → Prop

/-- The canonical rough spacetime quadruple extracted from an admissible physical instantiation. -/
def extractRoughSpacetimeQuadruple (I : AdmissiblePhysicalInstantiation) :
    RoughSpacetimeQuadruple I.State where
  causalPreorder := I.causalCompatibility.causalPreorder
  timeProjection := I.observerSpacetime.timeProjection
  resourceQuasidistance := I.resourceQuasidistance.resourceQuasidistance
  obstruction := I.obstructionInterface.obstruction

/-- The causal component of the extracted quadruple comes from the causal-compatibility
interface. -/
theorem extract_causal_preorder
    (I : AdmissiblePhysicalInstantiation) :
    (extractRoughSpacetimeQuadruple I).causalPreorder = I.causalCompatibility.causalPreorder :=
  rfl

/-- The temporal component of the extracted quadruple comes from the observer-spacetime
interface. -/
theorem extract_time_projection
    (I : AdmissiblePhysicalInstantiation) :
    (extractRoughSpacetimeQuadruple I).timeProjection = I.observerSpacetime.timeProjection :=
  rfl

/-- The resource component of the extracted quadruple comes from the resource-quasidistance
interface. -/
theorem extract_resource_quasidistance
    (I : AdmissiblePhysicalInstantiation) :
    (extractRoughSpacetimeQuadruple I).resourceQuasidistance =
      I.resourceQuasidistance.resourceQuasidistance :=
  rfl

/-- The obstruction component of the extracted quadruple comes from the obstruction interface. -/
theorem extract_obstruction
    (I : AdmissiblePhysicalInstantiation) :
    (extractRoughSpacetimeQuadruple I).obstruction = I.obstructionInterface.obstruction :=
  rfl

/-- Paper-facing wrapper: every admissible typed-address physical instantiation canonically
induces the rough spacetime quadruple whose four components are read off from the
observer-spacetime, causal-compatibility, resource-quasidistance, and obstruction interfaces.
    prop:typed-address-biaxial-completion-instantiation-extraction -/
theorem paper_typed_address_biaxial_completion_instantiation_extraction
    (I : AdmissiblePhysicalInstantiation) :
    ∃ G : RoughSpacetimeQuadruple I.State,
      G.causalPreorder = I.causalCompatibility.causalPreorder ∧
      G.timeProjection = I.observerSpacetime.timeProjection ∧
      G.resourceQuasidistance = I.resourceQuasidistance.resourceQuasidistance ∧
      G.obstruction = I.obstructionInterface.obstruction := by
  refine ⟨extractRoughSpacetimeQuadruple I, ?_⟩
  exact
    ⟨extract_causal_preorder I, extract_time_projection I, extract_resource_quasidistance I,
      extract_obstruction I⟩

end Omega.TypedAddressBiaxialCompletion
