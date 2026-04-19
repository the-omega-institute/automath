import Mathlib.Tactic

namespace Omega.Discussion

/-- A protocol exposes an observable and a verifier view on the same hidden state space. -/
structure NoHairProtocol (State Observation View : Type*) where
  observable : State → Observation
  verifierView : State → View

/-- "No hair" means that the verifier view depends only on the observable fiber. -/
def NoHair {State Observation View : Type*} (P : NoHairProtocol State Observation View) : Prop :=
  ∀ ⦃s t : State⦄, P.observable s = P.observable t → P.verifierView s = P.verifierView t

/-- Statistical zero knowledge is modeled here by a simulator reproducing the verifier view from
the observable alone. -/
def HasSimulator {State Observation View : Type*} (P : NoHairProtocol State Observation View) :
    Prop :=
  ∃ simulator : Observation → View, ∀ s : State,
    simulator (P.observable s) = P.verifierView s

/-- Choose a verifier-view representative on each nonempty observable fiber. -/
noncomputable def simulatorFromNoHair
    {State Observation View : Type*} [Inhabited View]
    (P : NoHairProtocol State Observation View) (_hNoHair : NoHair P) : Observation → View := by
  classical
  intro o
  exact if hFiber : ∃ s : State, P.observable s = o then
    P.verifierView (Classical.choose hFiber)
  else
    default

theorem simulatorFromNoHair_spec
    {State Observation View : Type*} [Inhabited View]
    (P : NoHairProtocol State Observation View) (hNoHair : NoHair P) (s : State) :
    simulatorFromNoHair P hNoHair (P.observable s) = P.verifierView s := by
  classical
  let hFiber : ∃ t : State, P.observable t = P.observable s := ⟨s, rfl⟩
  simpa [simulatorFromNoHair, hFiber] using hNoHair (Classical.choose_spec hFiber)

theorem hasSimulator_of_noHair
    {State Observation View : Type*} [Inhabited View]
    (P : NoHairProtocol State Observation View) (hNoHair : NoHair P) : HasSimulator P := by
  refine ⟨simulatorFromNoHair P hNoHair, ?_⟩
  intro s
  exact simulatorFromNoHair_spec P hNoHair s

theorem noHair_of_hasSimulator
    {State Observation View : Type*}
    (P : NoHairProtocol State Observation View) (hSimulator : HasSimulator P) : NoHair P := by
  rcases hSimulator with ⟨simulator, hSimulator⟩
  intro s t hObs
  calc
    P.verifierView s = simulator (P.observable s) := by symm; exact hSimulator s
    _ = simulator (P.observable t) := by simp [hObs]
    _ = P.verifierView t := hSimulator t

/-- Paper-facing equivalence: a verifier view is simulable from observables exactly when it is
constant on observable fibers.
    prop:discussion-nohair-iff-zk -/
theorem paper_discussion_nohair_iff_zk
    {State Observation View : Type*} [Inhabited View]
    (P : NoHairProtocol State Observation View) :
    NoHair P ↔ HasSimulator P := by
  exact ⟨hasSimulator_of_noHair P, noHair_of_hasSimulator P⟩

end Omega.Discussion
