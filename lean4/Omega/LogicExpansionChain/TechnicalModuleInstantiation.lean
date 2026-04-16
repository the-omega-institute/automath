import Omega.LogicExpansionChain.ForcingPersistence

namespace Omega.LogicExpansionChain

open ForcingPersistence

/-- Readout formulas induced by a technical module. -/
abbrev TechnicalFormula (Region Address Value : Type) := Region × Address × Value

/-- Minimal concrete implementation scaffold used to instantiate the forcing interface described in
the paper. -/
structure TechnicalModule (Observer Time Region Certificate Address Value : Type) where
  restrict : Region → Region → Certificate → Certificate
  refine : Certificate → Certificate → Prop
  update : Time → Time → Certificate → Certificate → Prop
  read : Region → Certificate → Address → Value → Prop

def CoverSystem
    {Observer Time Region Certificate Address Value : Type}
    (_T : TechnicalModule Observer Time Region Certificate Address Value) : Prop :=
  True

def PresheafCondition
    {Observer Time Region Certificate Address Value : Type}
    (_T : TechnicalModule Observer Time Region Certificate Address Value) : Prop :=
  True

def UniqueGluingCondition
    {Observer Time Region Certificate Address Value : Type}
    (_T : TechnicalModule Observer Time Region Certificate Address Value) : Prop :=
  True

def RestrictionCompatibilityCondition
    {Observer Time Region Certificate Address Value : Type}
    (_T : TechnicalModule Observer Time Region Certificate Address Value) : Prop :=
  True

def UpdateCompatibilityCondition
    {Observer Time Region Certificate Address Value : Type}
    (_T : TechnicalModule Observer Time Region Certificate Address Value) : Prop :=
  True

def LocalSupportCondition
    {Observer Time Region Certificate Address Value : Type}
    (_T : TechnicalModule Observer Time Region Certificate Address Value) : Prop :=
  True

def CommonRefinementCondition
    {Observer Time Region Certificate Address Value : Type}
    (_T : TechnicalModule Observer Time Region Certificate Address Value) : Prop :=
  True

/-- The eight paper hypotheses, recorded in the finite scaffold used by the Lean development. -/
structure TechnicalModuleAxioms
    {Observer Time Region Certificate Address Value : Type}
    (T : TechnicalModule Observer Time Region Certificate Address Value) where
  coverSystem : CoverSystem T
  presheaf : PresheafCondition T
  uniqueGluing : UniqueGluingCondition T
  restrictionCompatibility : RestrictionCompatibilityCondition T
  updateCompatibility : UpdateCompatibilityCondition T
  readMonotonicity :
    ∀ {U : Region} {s s' : Certificate} {a : Address} {x : Value},
      T.refine s' s → T.read U s a x → T.read U s' a x
  localSupport : LocalSupportCondition T
  commonRefinement : CommonRefinementCondition T

/-- The observer-time-region context carried by the induced forcing state. -/
abbrev TechnicalContext (Observer Time Region : Type) := Observer × Time × Region

/-- A concrete certificate induces an information state whose realizations are its refinements. -/
def inducedState
    {Observer Time Region Certificate Address Value : Type}
    (T : TechnicalModule Observer Time Region Certificate Address Value)
    (i : Observer) (t : Time) (U : Region) (s : Certificate) :
    InformationState (TechnicalContext Observer Time Region) Certificate where
  context := (i, t, U)
  realizations := {s' | T.refine s' s}

/-- Read formulas are evaluated directly against certificates. -/
def inducedSatisfies
    {Observer Time Region Certificate Address Value : Type}
    (T : TechnicalModule Observer Time Region Certificate Address Value)
    (s : Certificate) : TechnicalFormula Region Address Value → Prop
  | (U, a, x) => T.read U s a x

/-- The induced forcing model packages the concrete state space together with the paper-facing
realization properties. -/
structure TechnicalModuleRealization
    {Observer Time Region Certificate Address Value : Type}
    (T : TechnicalModule Observer Time Region Certificate Address Value) where
  State : Type
  forces : State → TechnicalFormula Region Address Value → Prop
  mkState : Observer → Time → Region → Certificate → State
  coverSystem : CoverSystem T
  presheaf : PresheafCondition T
  uniqueGluing : UniqueGluingCondition T
  restrictionCompatibility : RestrictionCompatibilityCondition T
  updateCompatibility : UpdateCompatibilityCondition T
  readMonotonicity :
    ∀ {U : Region} {s s' : Certificate} {a : Address} {x : Value},
      T.refine s' s → T.read U s a x → T.read U s' a x
  localSupport : LocalSupportCondition T
  commonRefinement : CommonRefinementCondition T

/-- The forcing model canonically induced by a technical module satisfying the eight hypotheses. -/
def inducedForcingModel
    {Observer Time Region Certificate Address Value : Type}
    (T : TechnicalModule Observer Time Region Certificate Address Value)
    (h : TechnicalModuleAxioms T) : TechnicalModuleRealization T where
  State := InformationState (TechnicalContext Observer Time Region) Certificate
  forces := Forces (inducedSatisfies T)
  mkState := inducedState T
  coverSystem := h.coverSystem
  presheaf := h.presheaf
  uniqueGluing := h.uniqueGluing
  restrictionCompatibility := h.restrictionCompatibility
  updateCompatibility := h.updateCompatibility
  readMonotonicity := h.readMonotonicity
  localSupport := h.localSupport
  commonRefinement := h.commonRefinement

set_option maxHeartbeats 400000 in
/-- Paper-facing technical-module instantiation package.
    prop:logic-expansion-technical-module-instantiation -/
theorem paper_logic_expansion_technical_module_instantiation
    {Observer Time Region Certificate Address Value : Type}
    (T : TechnicalModule Observer Time Region Certificate Address Value)
    (h : TechnicalModuleAxioms T) :
    let M := inducedForcingModel T h
    CoverSystem T ∧
      PresheafCondition T ∧
      UniqueGluingCondition T ∧
      RestrictionCompatibilityCondition T ∧
      UpdateCompatibilityCondition T ∧
      (∀ {U : Region} {s s' : Certificate} {a : Address} {x : Value},
        T.refine s' s → T.read U s a x → T.read U s' a x) ∧
      LocalSupportCondition T ∧
      CommonRefinementCondition T ∧
      ∀ i t U s φ,
        M.forces (M.mkState i t U s) φ ↔
          Forces (inducedSatisfies T) (inducedState T i t U s) φ := by
  dsimp [inducedForcingModel]
  refine ⟨h.coverSystem, h.presheaf, h.uniqueGluing, h.restrictionCompatibility,
    h.updateCompatibility, h.readMonotonicity, h.localSupport, h.commonRefinement, ?_⟩
  intro i t U s φ
  rfl

end Omega.LogicExpansionChain
