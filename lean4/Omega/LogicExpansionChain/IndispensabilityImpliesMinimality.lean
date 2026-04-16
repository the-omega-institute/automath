import Mathlib.Data.Finset.Basic

namespace Omega.LogicExpansionChain

/-- A state decides `φ` when it forces either `φ` or its designated negation. -/
def Decides
    {State Formula : Type}
    (Forces : State → Formula → Prop) (neg : Formula → Formula)
    (s : State) (φ : Formula) : Prop :=
  Forces s φ ∨ Forces s (neg φ)

/-- `K` supports `φ` at `p` when any two `K`-successors that are `K`-indistinguishable and both
decide `φ` agree on whether `φ` is forced. This is the paper-facing finite-axis abstraction of
`K ▷ₚ φ`. -/
def AxisSupports
    {State Axis Formula : Type}
    (Reach : Finset Axis → State → State → Prop)
    (Agree : Finset Axis → State → State → Prop)
    (Forces : State → Formula → Prop)
    (neg : Formula → Formula)
    (K : Finset Axis) (p : State) (φ : Formula) : Prop :=
  ∀ ⦃q r : State⦄,
    Reach K p q →
    Reach K p r →
    Agree K q r →
    Decides Forces neg q φ →
    Decides Forces neg r φ →
    (Forces q φ ↔ Forces r φ)

/-- A paper-facing finite-set formulation of minimal axis support. -/
def MinimalAxisSupport
    {State Axis Formula : Type}
    (Reach : Finset Axis → State → State → Prop)
    (Agree : Finset Axis → State → State → Prop)
    (Forces : State → Formula → Prop)
    (neg : Formula → Formula)
    (K : Finset Axis) (p : State) (φ : Formula) : Prop :=
  AxisSupports Reach Agree Forces neg K p φ ∧
    ∀ L : Finset Axis, L ⊂ K → ¬ AxisSupports Reach Agree Forces neg L p φ

/-- Relative indispensability for an axis `j ∈ K`: after deleting `j`, there is still a pair of
`K`-successors that remain indistinguishable on the smaller support but force opposite decisions. -/
def RelativelyIndispensable
    {State Axis Formula : Type} [DecidableEq Axis]
    (Reach : Finset Axis → State → State → Prop)
    (Agree : Finset Axis → State → State → Prop)
    (Forces : State → Formula → Prop)
    (neg : Formula → Formula)
    (K : Finset Axis) (p : State) (j : Axis) (φ : Formula) : Prop :=
  ∃ q r : State,
    Reach K p q ∧
    Reach K p r ∧
    Agree (K.erase j) q r ∧
    Forces q φ ∧
    Forces r (neg φ)

set_option maxHeartbeats 400000 in
/-- Paper-facing wrapper: if `K` supports `φ` and every axis in `K` is relatively indispensable,
then `K` is already a minimal support. The proof follows the paper's contradiction argument by
choosing an omitted axis from a smaller supporting set.
    prop:logic-expansion-indispensability-implies-minimality -/
theorem paper_logic_expansion_indispensability_implies_minimality
    {State Axis Formula : Type} [DecidableEq Axis]
    (Reach : Finset Axis → State → State → Prop)
    (Agree : Finset Axis → State → State → Prop)
    (Forces : State → Formula → Prop)
    (neg : Formula → Formula)
    (hReachMono :
      ∀ ⦃L K : Finset Axis⦄ ⦃p q : State⦄, L ⊆ K → Reach K p q → Reach L p q)
    (hAgreeMono :
      ∀ ⦃L K : Finset Axis⦄ ⦃q r : State⦄, L ⊆ K → Agree K q r → Agree L q r)
    (hNoConflict :
      ∀ {s : State} {φ : Formula}, ¬ (Forces s φ ∧ Forces s (neg φ)))
    {K : Finset Axis} {p : State} {φ : Formula}
    (hSupport : AxisSupports Reach Agree Forces neg K p φ)
    (hInd :
      ∀ j : Axis, j ∈ K → RelativelyIndispensable Reach Agree Forces neg K p j φ) :
    MinimalAxisSupport Reach Agree Forces neg K p φ := by
  refine ⟨hSupport, ?_⟩
  intro L hL hLSupport
  rcases Finset.exists_of_ssubset hL with ⟨j, hjK, hjL⟩
  rcases hInd j hjK with ⟨q, r, hq, hr, hAgreeErase, hqForce, hrNeg⟩
  have hSubset : L ⊆ K.erase j := by
    intro a haL
    have haK : a ∈ K := hL.1 haL
    have haNe : a ≠ j := by
      intro hEq
      subst hEq
      exact hjL haL
    exact Finset.mem_erase.mpr ⟨haNe, haK⟩
  have hqL : Reach L p q := hReachMono hL.1 hq
  have hrL : Reach L p r := hReachMono hL.1 hr
  have hAgreeL : Agree L q r := hAgreeMono hSubset hAgreeErase
  have hSameForce : Forces q φ ↔ Forces r φ :=
    hLSupport hqL hrL hAgreeL (Or.inl hqForce) (Or.inr hrNeg)
  have hrForce : Forces r φ := hSameForce.mp hqForce
  exact (hNoConflict (s := r) (φ := φ) ⟨hrForce, hrNeg⟩).elim

end Omega.LogicExpansionChain
