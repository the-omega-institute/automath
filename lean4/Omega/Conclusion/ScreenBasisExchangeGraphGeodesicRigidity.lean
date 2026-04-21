import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace Omega.Conclusion

open Finset

/-- Finite basis-exchange datum: every basis is represented by a finite set of the fixed
cardinality `basisSize`. -/
structure ScreenBasisExchangeData where
  Edge : Type
  decEqEdge : DecidableEq Edge
  basisSize : ℕ

attribute [instance] ScreenBasisExchangeData.decEqEdge

/-- Minimal exact screens are modeled as bases of fixed size. -/
def ScreenBasisExchangeData.IsBasis (D : ScreenBasisExchangeData) (B : Finset D.Edge) : Prop :=
  B.card = D.basisSize

/-- One exchange changes exactly one element of `B \ B'`. -/
def ScreenBasisExchangeData.basisExchangeDistance
    (D : ScreenBasisExchangeData) (B B' : Finset D.Edge) : ℕ :=
  (B \ B').card

/-- Arithmetic screen distance, encoded as the symmetric-difference cardinality. -/
def ScreenBasisExchangeData.arithmeticDistance
    (D : ScreenBasisExchangeData) (B B' : Finset D.Edge) : ℕ :=
  (B \ B').card + (B' \ B).card

/-- The basis-exchange graph distance is rigid: for two bases it equals half the symmetric
difference cardinality. -/
def ScreenBasisExchangeGraphGeodesicRigidity (D : ScreenBasisExchangeData)
    (B B' : Finset D.Edge) : Prop :=
  D.basisExchangeDistance B B' = D.arithmeticDistance B B' / 2

/-- Paper label: `thm:conclusion-screen-basis-exchange-graph-geodesic-rigidity`. -/
theorem paper_conclusion_screen_basis_exchange_graph_geodesic_rigidity
    (D : ScreenBasisExchangeData) {B B' : Finset D.Edge}
    (hB : D.IsBasis B) (hB' : D.IsBasis B') :
    ScreenBasisExchangeGraphGeodesicRigidity D B B' := by
  have hcard : B.card = B'.card := by
    calc
      B.card = D.basisSize := hB
      _ = B'.card := hB'.symm
  have hsdiff : (B \ B').card = (B' \ B).card := Finset.card_sdiff_comm hcard
  unfold ScreenBasisExchangeGraphGeodesicRigidity
  unfold ScreenBasisExchangeData.basisExchangeDistance ScreenBasisExchangeData.arithmeticDistance
  omega

end Omega.Conclusion
