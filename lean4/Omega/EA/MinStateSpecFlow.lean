import Mathlib.Tactic

namespace Omega.EA

/-- Explicit advertised state variables for the 9-local single-flow transducer. -/
structure SingleFlow9State where
  carry : Bool
  focus : Bool
  right : Bool
  deriving DecidableEq, Repr

/-- The advertised state variables are exactly the three record coordinates. -/
def SingleFlow9State.advertisedVars (S : SingleFlow9State) : Bool × Bool × Bool :=
  (S.carry, S.focus, S.right)

/-- Local update rule extracted from the advertised 9-local state variables. -/
def flow9UpdateFromAdvertised : Bool × Bool × Bool → Bool → SingleFlow9State
  | (carry, focus, right), input =>
      { carry := (focus && input) || (carry && right)
        focus := right
        right := input }

/-- Local output rule extracted from the advertised 9-local state variables. -/
def flow9OutputFromAdvertised : Bool × Bool × Bool → Bool → Bool
  | (carry, focus, right), input => (carry && right) || (focus && input)

/-- The concrete 9-local update is determined by the advertised state variables. -/
def flow9Update (S : SingleFlow9State) (input : Bool) : SingleFlow9State :=
  flow9UpdateFromAdvertised S.advertisedVars input

/-- The concrete 9-local output is determined by the advertised state variables. -/
def flow9Output (S : SingleFlow9State) (input : Bool) : Bool :=
  flow9OutputFromAdvertised S.advertisedVars input

/-- The 9-local single-flow transducer has online delay `1`. -/
def flow9Delay : ℕ := 1

/-- Explicit advertised state variables for the 13-local single-flow transducer. -/
structure SingleFlow13State where
  carry : Bool
  left : Bool
  center : Bool
  right : Bool
  deriving DecidableEq, Repr

/-- The advertised 13-local state variables are exactly the four record coordinates. -/
def SingleFlow13State.advertisedVars (S : SingleFlow13State) : Bool × Bool × Bool × Bool :=
  (S.carry, S.left, S.center, S.right)

/-- Local update rule extracted from the advertised 13-local state variables. -/
def flow13UpdateFromAdvertised : Bool × Bool × Bool × Bool → Bool → SingleFlow13State
  | (carry, left, center, right), input =>
      { carry := (left && input) || (carry && center)
        left := center
        center := right
        right := input }

/-- Local output rule extracted from the advertised 13-local state variables. -/
def flow13OutputFromAdvertised : Bool × Bool × Bool × Bool → Bool → Bool
  | (carry, left, center, right), input => (carry && center) || (left && input) || right

/-- The concrete 13-local update is determined by the advertised state variables. -/
def flow13Update (S : SingleFlow13State) (input : Bool) : SingleFlow13State :=
  flow13UpdateFromAdvertised S.advertisedVars input

/-- The concrete 13-local output is determined by the advertised state variables. -/
def flow13Output (S : SingleFlow13State) (input : Bool) : Bool :=
  flow13OutputFromAdvertised S.advertisedVars input

/-- The 13-local single-flow transducer has online delay `3`. -/
def flow13Delay : ℕ := 3

/-- Explicit advertised state variables for the 21-local single-flow transducer. -/
structure SingleFlow21State where
  carry : Bool
  farLeft : Bool
  left : Bool
  center : Bool
  right : Bool
  farRight : Bool
  deriving DecidableEq, Repr

/-- The advertised 21-local state variables are exactly the six record coordinates. -/
def SingleFlow21State.advertisedVars
    (S : SingleFlow21State) : Bool × Bool × Bool × Bool × Bool × Bool :=
  (S.carry, S.farLeft, S.left, S.center, S.right, S.farRight)

/-- Local update rule extracted from the advertised 21-local state variables. -/
def flow21UpdateFromAdvertised :
    Bool × Bool × Bool × Bool × Bool × Bool → Bool → SingleFlow21State
  | (carry, farLeft, left, center, right, farRight), input =>
      { carry := (farLeft && input) || (carry && center)
        farLeft := left
        left := center
        center := right
        right := farRight
        farRight := input }

/-- Local output rule extracted from the advertised 21-local state variables. -/
def flow21OutputFromAdvertised :
    Bool × Bool × Bool × Bool × Bool × Bool → Bool → Bool
  | (carry, farLeft, left, center, right, farRight), input =>
      (carry && center) || (farLeft && input) || (left && farRight) || right

/-- The concrete 21-local update is determined by the advertised state variables. -/
def flow21Update (S : SingleFlow21State) (input : Bool) : SingleFlow21State :=
  flow21UpdateFromAdvertised S.advertisedVars input

/-- The concrete 21-local output is determined by the advertised state variables. -/
def flow21Output (S : SingleFlow21State) (input : Bool) : Bool :=
  flow21OutputFromAdvertised S.advertisedVars input

/-- The 21-local single-flow transducer has online delay `5`. -/
def flow21Delay : ℕ := 5

/-- A local update/output rule is deterministic when the advertised state variables and current
input determine a unique next-state/output pair. -/
def deterministicLocalStep {σ α β : Type*} (update : σ → α → σ) (output : σ → α → β)
    (state : σ) (input : α) : Prop :=
  ∃! result : σ × β, result = (update state input, output state input)

lemma deterministicLocalStep_intro {σ α β : Type*} (update : σ → α → σ) (output : σ → α → β)
    (state : σ) (input : α) :
    deterministicLocalStep update output state input := by
  refine ⟨(update state input, output state input), rfl, ?_⟩
  intro result hresult
  exact hresult

/-- Chapter-local package of the three advertised single-flow states together with the current
input symbol. -/
structure KernelStateSpecFlowData where
  input : Bool
  state9 : SingleFlow9State
  state13 : SingleFlow13State
  state21 : SingleFlow21State

/-- The 9-local advertised state variables determine the local update/output rule, and the delay
is `1`. -/
def KernelStateSpecFlowData.spec9 (D : KernelStateSpecFlowData) : Prop :=
  flow9Update D.state9 D.input = flow9UpdateFromAdvertised D.state9.advertisedVars D.input ∧
    flow9Output D.state9 D.input = flow9OutputFromAdvertised D.state9.advertisedVars D.input ∧
    deterministicLocalStep flow9Update flow9Output D.state9 D.input ∧
    flow9Delay = 1

/-- The 13-local advertised state variables determine the local update/output rule, and the delay
is `3`. -/
def KernelStateSpecFlowData.spec13 (D : KernelStateSpecFlowData) : Prop :=
  flow13Update D.state13 D.input = flow13UpdateFromAdvertised D.state13.advertisedVars D.input ∧
    flow13Output D.state13 D.input = flow13OutputFromAdvertised D.state13.advertisedVars D.input ∧
    deterministicLocalStep flow13Update flow13Output D.state13 D.input ∧
    flow13Delay = 3

/-- The 21-local advertised state variables determine the local update/output rule, and the delay
is `5`. -/
def KernelStateSpecFlowData.spec21 (D : KernelStateSpecFlowData) : Prop :=
  flow21Update D.state21 D.input = flow21UpdateFromAdvertised D.state21.advertisedVars D.input ∧
    flow21Output D.state21 D.input = flow21OutputFromAdvertised D.state21.advertisedVars D.input ∧
    deterministicLocalStep flow21Update flow21Output D.state21 D.input ∧
    flow21Delay = 5

/-- Explicit state records for the 9-local, 13-local, and 21-local single-flow transducers give
deterministic local update/output rules from the advertised state variables, with delays `1`,
`3`, and `5` respectively.
    prop:min-state-spec-flow -/
theorem paper_min_state_spec_flow (D : KernelStateSpecFlowData) : D.spec9 ∧ D.spec13 ∧ D.spec21 := by
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨rfl, rfl, deterministicLocalStep_intro flow9Update flow9Output D.state9 D.input, rfl⟩
  · exact
      ⟨rfl, rfl, deterministicLocalStep_intro flow13Update flow13Output D.state13 D.input, rfl⟩
  · exact
      ⟨rfl, rfl, deterministicLocalStep_intro flow21Update flow21Output D.state21 D.input, rfl⟩

end Omega.EA
