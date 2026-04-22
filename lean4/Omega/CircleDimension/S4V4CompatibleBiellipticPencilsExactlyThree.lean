import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace Omega.CircleDimension

/-- The compatible bielliptic pencils are indexed by the three order-`2` subgroups of the
`S₃`-closure. The Lean model keeps just the resulting `3`-element packet. -/
abbrev S4V4CompatibleBiellipticPencil := Fin 3

/-- The finite packet of compatible pencils. -/
def s4v4CompatibleBiellipticPencils : Finset S4V4CompatibleBiellipticPencil :=
  Finset.univ

/-- The `C₃`-action is the cyclic shift on the three indexed pencils. -/
def s4v4CompatibleBiellipticC3Action
    (k i : S4V4CompatibleBiellipticPencil) : S4V4CompatibleBiellipticPencil :=
  i + k

/-- The orbit map from a chosen base pencil. -/
def s4v4CompatibleBiellipticOrbitMap
    (k : S4V4CompatibleBiellipticPencil) : S4V4CompatibleBiellipticPencil :=
  s4v4CompatibleBiellipticC3Action k 0

/-- The cyclic action is simply transitive: from the base pencil, every target pencil is reached by
exactly one element of `C₃`. -/
def s4v4CompatibleBiellipticC3ActsSimplyTransitively : Prop :=
  Function.Bijective s4v4CompatibleBiellipticOrbitMap

private lemma s4v4CompatibleBiellipticPencils_card :
    s4v4CompatibleBiellipticPencils.card = 3 := by
  simp [s4v4CompatibleBiellipticPencils]

private lemma s4v4CompatibleBiellipticOrbitMap_bijective :
    Function.Bijective s4v4CompatibleBiellipticOrbitMap := by
  refine ⟨?_, ?_⟩
  · intro k₁ k₂ hk
    simpa [s4v4CompatibleBiellipticOrbitMap, s4v4CompatibleBiellipticC3Action] using hk
  · intro i
    refine ⟨i, ?_⟩
    simp [s4v4CompatibleBiellipticOrbitMap, s4v4CompatibleBiellipticC3Action]

/-- Paper label: `thm:cdim-s4-v4-compatible-bielliptic-pencils-exactly-three`.
The compatible bielliptic pencils form a `3`-element packet, and the induced `C₃`-action is simply
transitive. -/
theorem paper_cdim_s4_v4_compatible_bielliptic_pencils_exactly_three :
    s4v4CompatibleBiellipticPencils.card = 3 ∧
      s4v4CompatibleBiellipticC3ActsSimplyTransitively := by
  exact ⟨s4v4CompatibleBiellipticPencils_card,
    s4v4CompatibleBiellipticOrbitMap_bijective⟩

end Omega.CircleDimension
