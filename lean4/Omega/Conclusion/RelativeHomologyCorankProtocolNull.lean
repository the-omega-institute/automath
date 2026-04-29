import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Omega.Conclusion.ScreenRelativeBettiRenyiFlatness
import Omega.SPG.RegisterLowerBound

namespace Omega.Conclusion

open ScreenFlatFiberData

/-- Concrete screen data for the relative-homology/corank protocol-null package. The visible
fibers all have the same dyadic cardinality `2^beta`, and the `Unit` register models the
no-hidden-side-information discipline. -/
structure RelativeHomologyCorankProtocolNullData where
  Source : Type
  Screen : Type
  sourceFintype : Fintype Source
  screenDecidableEq : DecidableEq Screen
  screenReadout : Source → Screen
  witness : Source
  flatFiber : ScreenFlatFiberData
  visibleFiberCardinality :
    ∀ y : Set.range screenReadout,
      Fintype.card {x : Source // screenReadout x = y.1} = flatFiber.fiberCardinality

attribute [instance] RelativeHomologyCorankProtocolNullData.sourceFintype
attribute [instance] RelativeHomologyCorankProtocolNullData.screenDecidableEq

namespace RelativeHomologyCorankProtocolNullData

/-- Relative Betti positivity is read as positivity of the flat conditional entropy. -/
def relativeBettiPos (D : RelativeHomologyCorankProtocolNullData) : Prop :=
  0 < D.flatFiber.shannonCond

/-- Zero corank means vanishing relative Betti number. -/
def relativeBettiZero (D : RelativeHomologyCorankProtocolNullData) : Prop :=
  D.flatFiber.shannonCond = 0

/-- A visible fiber is nontrivial when it contains more than one source state. -/
def hasNontrivialFiber (D : RelativeHomologyCorankProtocolNullData) : Prop :=
  ∃ y : Set.range D.screenReadout, 1 < Fintype.card {x : D.Source // D.screenReadout x = y.1}

/-- Protocol-null means that, with no hidden side information beyond a `Unit` register, the screen
readout cannot be made injective. -/
def protocolNullOccurs (D : RelativeHomologyCorankProtocolNullData) : Prop :=
  ¬ ∃ r : D.Source → Unit, Function.Injective fun x => (D.screenReadout x, r x)

/-- Injectivity of the visible screen readout. -/
def screenReadoutInjective (D : RelativeHomologyCorankProtocolNullData) : Prop :=
  Function.Injective D.screenReadout

private lemma one_lt_two_pow_of_pos {β : ℕ} (hβ : 0 < β) : 1 < 2 ^ β := by
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hβ) with ⟨k, rfl⟩
  have hk : 1 ≤ 2 ^ k := Nat.succ_le_of_lt (pow_pos (by decide : 0 < 2) _)
  have hmul : 2 ≤ 2 * 2 ^ k := Nat.mul_le_mul_left 2 hk
  have htwo : 1 < 2 := by decide
  simpa [Nat.pow_succ, Nat.mul_comm] using lt_of_lt_of_le htwo hmul

lemma injective_of_no_nontrivialFiber (D : RelativeHomologyCorankProtocolNullData)
    (h : ¬ D.hasNontrivialFiber) : D.screenReadoutInjective := by
  intro x₁ x₂ hEq
  let y : Set.range D.screenReadout := ⟨D.screenReadout x₁, x₁, rfl⟩
  have hnot : ¬ 1 < Fintype.card {x : D.Source // D.screenReadout x = y.1} := by
    intro hlt
    exact h ⟨y, hlt⟩
  have hle : Fintype.card {x : D.Source // D.screenReadout x = y.1} ≤ 1 := Nat.le_of_not_gt hnot
  have hsub : Subsingleton {x : D.Source // D.screenReadout x = y.1} := by
    rw [← Fintype.card_le_one_iff_subsingleton]
    exact hle
  have hx :
      (⟨x₁, rfl⟩ : {x : D.Source // D.screenReadout x = y.1}) =
        ⟨x₂, by simpa [y] using hEq.symm⟩ := by
    exact Subsingleton.elim _ _
  exact congrArg Subtype.val hx

end RelativeHomologyCorankProtocolNullData

open RelativeHomologyCorankProtocolNullData

/-- Paper label: `thm:conclusion-relative-homology-corank-protocol-null`. -/
theorem paper_conclusion_relative_homology_corank_protocol_null
    (D : RelativeHomologyCorankProtocolNullData) :
    (D.relativeBettiPos ↔ D.hasNontrivialFiber) ∧
      (D.hasNontrivialFiber ↔ D.protocolNullOccurs) ∧
      (D.relativeBettiZero → D.screenReadoutInjective) := by
  have hflat := paper_conclusion_relative_betti_renyi_flatness D.flatFiber
  have hcond : D.flatFiber.shannonCond = D.flatFiber.beta := hflat.1
  have hBettiFiber : D.relativeBettiPos ↔ D.hasNontrivialFiber := by
    constructor
    · intro hPos
      let y : Set.range D.screenReadout := ⟨D.screenReadout D.witness, D.witness, rfl⟩
      refine ⟨y, ?_⟩
      have hβ : 0 < D.flatFiber.beta := by
        simpa [RelativeHomologyCorankProtocolNullData.relativeBettiPos, hcond] using hPos
      rw [D.visibleFiberCardinality y]
      simpa [ScreenFlatFiberData.fiberCardinality] using one_lt_two_pow_of_pos hβ
    · intro hFiber
      rcases hFiber with ⟨y, hy⟩
      have hβ : 0 < D.flatFiber.beta := by
        by_contra hβ
        have hβ0 : D.flatFiber.beta = 0 := Nat.eq_zero_of_not_pos hβ
        have hcard :
            Fintype.card {x : D.Source // D.screenReadout x = y.1} = 1 := by
          rw [D.visibleFiberCardinality y, ScreenFlatFiberData.fiberCardinality, hβ0]
          simp
        omega
      simpa [RelativeHomologyCorankProtocolNullData.relativeBettiPos, hcond] using hβ
  have hFiberProtocol : D.hasNontrivialFiber ↔ D.protocolNullOccurs := by
    constructor
    · intro hFiber
      intro hInjectivize
      rcases hFiber with ⟨y, hy⟩
      rcases hInjectivize with ⟨r, hr⟩
      have hbound :
          Fintype.card {x : D.Source // D.screenReadout x = y.1} ≤ Fintype.card Unit :=
        Omega.SPG.RegisterLowerBound.paper_scan_projection_address_register_lower_bound
          (f := D.screenReadout) (r := r) hr y.1
      simp at hbound
      omega
    · intro hNull
      by_contra hNoFiber
      have hinj :
          D.screenReadoutInjective :=
        D.injective_of_no_nontrivialFiber hNoFiber
      have hUnit :
          ∃ r : D.Source → Unit, Function.Injective fun x => (D.screenReadout x, r x) := by
        refine ⟨fun _ => (), ?_⟩
        intro x₁ x₂ hEq
        apply hinj
        exact congrArg Prod.fst hEq
      exact hNull hUnit
  have hZeroInjective : D.relativeBettiZero → D.screenReadoutInjective := by
    intro hZero
    apply D.injective_of_no_nontrivialFiber
    intro hFiber
    rcases hFiber with ⟨y, hy⟩
    have hβ0 : D.flatFiber.beta = 0 := by
      simpa [RelativeHomologyCorankProtocolNullData.relativeBettiZero, hcond] using hZero
    have hcard : Fintype.card {x : D.Source // D.screenReadout x = y.1} = 1 := by
      rw [D.visibleFiberCardinality y, ScreenFlatFiberData.fiberCardinality, hβ0]
      simp
    omega
  exact ⟨hBettiFiber, hFiberProtocol, hZeroInjective⟩

end Omega.Conclusion
