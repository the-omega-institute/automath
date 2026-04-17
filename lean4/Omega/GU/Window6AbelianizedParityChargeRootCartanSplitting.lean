import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Omega.GU.Window6AdjointWeightMultiset
import Omega.GU.Window6CyclicWeightThresholdRootLength

namespace Omega.GU

/-- The six short-root coordinates in the window-6 parity lattice. -/
abbrev Window6ShortRootParityBlock := Fin 6

/-- The twelve long-root coordinates in the window-6 parity lattice. -/
abbrev Window6LongRootParityBlock := Fin 12

/-- The three boundary coordinates, identified with the Cartan zero-weight sector. -/
abbrev Window6BoundaryParityBlock := Fin 3

/-- The full list of window-6 parity coordinates. -/
abbrev Window6ParityCoordinate :=
  (Window6ShortRootParityBlock ⊕ Window6LongRootParityBlock) ⊕ Window6BoundaryParityBlock

/-- All parity charges are taken over `F₂`. -/
abbrev Window6F2 := ZMod 2

/-- Short-root parity sector. -/
abbrev Window6ShortRootParityLattice := Window6ShortRootParityBlock → Window6F2

/-- Long-root parity sector. -/
abbrev Window6LongRootParityLattice := Window6LongRootParityBlock → Window6F2

/-- Boundary/Cartan parity sector. -/
abbrev Window6BoundaryParityLattice := Window6BoundaryParityBlock → Window6F2

/-- The full abelianized parity-charge lattice. -/
abbrev Window6AbelianizedParityCharge := Window6ParityCoordinate → Window6F2

/-- The canonical block decomposition of the `21` parity coordinates into `6 + 12 + 3`. -/
def window6AbelianizedParityChargeSplit :
    Window6AbelianizedParityCharge ≃
      (Window6ShortRootParityLattice × Window6LongRootParityLattice) ×
        Window6BoundaryParityLattice where
  toFun f :=
    ((fun i => f (.inl (.inl i)), fun j => f (.inl (.inr j))), fun k => f (.inr k))
  invFun blocks x :=
    match x with
    | .inl (.inl i) => blocks.1.1 i
    | .inl (.inr j) => blocks.1.2 j
    | .inr k => blocks.2 k
  left_inv f := by
    funext x
    cases x with
    | inl x =>
        cases x with
        | inl i => rfl
        | inr j => rfl
    | inr k => rfl
  right_inv blocks := by
    rcases blocks with ⟨⟨short, long⟩, boundary⟩
    rfl

/-- The boundary subgroup embeds as the Cartan summand of the abelianized parity lattice. -/
def window6BoundaryCartanInclusion :
    Window6BoundaryParityLattice → Window6AbelianizedParityCharge := fun boundary x =>
  match x with
  | .inl (.inl _) => 0
  | .inl (.inr _) => 0
  | .inr k => boundary k

/-- The Cartan projection forgets the short and long root coordinates. -/
def window6BoundaryCartanProjection :
    Window6AbelianizedParityCharge → Window6BoundaryParityLattice := fun charge k =>
  charge (.inr k)

theorem window6BoundaryCartanProjection_inclusion :
    Function.LeftInverse window6BoundaryCartanProjection window6BoundaryCartanInclusion := by
  intro boundary
  funext k
  rfl

/-- Paper-facing wrapper for the `6 + 12 + 3 = 21` root/Cartan splitting of the window-6
abelianized parity lattice. The `18` nonzero adjoint weights form the root part and the `3`
boundary zero weights form the Cartan summand.
    thm:window6-abelianized-parity-charge-root-cartan-splitting -/
theorem paper_window6_abelianized_parity_charge_root_cartan_splitting :
    (b3VisibleSupport.erase zeroWeight).card = 18 ∧
    (c3VisibleSupport.erase zeroWeight).card = 18 ∧
    boundaryZeroWeights.card = 3 ∧
    b3AdjointWeightMultiset.card = 21 ∧
    c3AdjointWeightMultiset.card = 21 ∧
    Fintype.card Window6ShortRootParityBlock = 6 ∧
    Fintype.card Window6LongRootParityBlock = 12 ∧
    Fintype.card Window6BoundaryParityBlock = 3 ∧
    Fintype.card Window6ParityCoordinate = 21 ∧
    Function.LeftInverse window6BoundaryCartanProjection window6BoundaryCartanInclusion ∧
    (∀ boundary,
      window6AbelianizedParityChargeSplit (window6BoundaryCartanInclusion boundary) =
        ((0, 0), boundary)) := by
  rcases paper_window6_21_adjoint_weight_multiset with
    ⟨_, hb3, hc3, hBoundary, hb3Adj, hc3Adj, _, _⟩
  refine ⟨hb3, hc3, hBoundary, hb3Adj, hc3Adj, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Window6ShortRootParityBlock]
  · simp [Window6LongRootParityBlock]
  · simp [Window6BoundaryParityBlock]
  · simp [Window6ParityCoordinate]
  · exact window6BoundaryCartanProjection_inclusion
  · intro boundary
    rfl

end Omega.GU
