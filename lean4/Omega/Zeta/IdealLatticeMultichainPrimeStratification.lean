import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/-- Lower ideals in a finite poset, represented as finite subsets. -/
def xi_ideal_lattice_multichain_prime_stratification_orderIdeal {P : Type*}
    [PartialOrder P] (I : Finset P) : Prop :=
  ∀ ⦃a b : P⦄, a ≤ b → b ∈ I → a ∈ I

/-- Increasing chains of lower ideals with terminal ideal equal to the whole finite poset. -/
def xi_ideal_lattice_multichain_prime_stratification_multichains (P : Type*)
    [Fintype P] [DecidableEq P] [PartialOrder P] (k : ℕ) : Type _ :=
  {I : Fin (k + 1) → Finset P //
    (∀ t, xi_ideal_lattice_multichain_prime_stratification_orderIdeal (I t)) ∧
      (∀ ⦃s t : Fin (k + 1)⦄, s ≤ t → I s ⊆ I t) ∧
      I (Fin.last k) = Finset.univ}

/-- Assignments of each prime/lattice element to one of the `k + 1` layers, preserving order. -/
def xi_ideal_lattice_multichain_prime_stratification_prime_layers (P : Type*)
    [PartialOrder P] (k : ℕ) : Type _ :=
  {L : P → Fin (k + 1) // ∀ ⦃a b : P⦄, a ≤ b → L a ≤ L b}

noncomputable instance xi_ideal_lattice_multichain_prime_stratification_multichains_fintype
    {P : Type*} [Fintype P] [DecidableEq P] [PartialOrder P] (k : ℕ) :
    Fintype (xi_ideal_lattice_multichain_prime_stratification_multichains P k) :=
  Fintype.ofInjective
    (fun I : xi_ideal_lattice_multichain_prime_stratification_multichains P k => I.1)
    (fun _ _ h => Subtype.ext h)

noncomputable instance xi_ideal_lattice_multichain_prime_stratification_prime_layers_fintype
    {P : Type*} [Fintype P] [DecidableEq P] [PartialOrder P] (k : ℕ) :
    Fintype (xi_ideal_lattice_multichain_prime_stratification_prime_layers P k) :=
  Fintype.ofInjective
    (fun L : xi_ideal_lattice_multichain_prime_stratification_prime_layers P k => L.1)
    (fun _ _ h => Subtype.ext h)

namespace xi_ideal_lattice_multichain_prime_stratification

variable {P : Type*} [Fintype P] [DecidableEq P] [PartialOrder P] {k : ℕ}

abbrev Multichain :=
  xi_ideal_lattice_multichain_prime_stratification_multichains P k

abbrev PrimeLayers :=
  xi_ideal_lattice_multichain_prime_stratification_prime_layers P k

/-- The set of indices whose ideal already contains `p`. -/
def layerSupport (I : Multichain (P := P) (k := k)) (p : P) : Finset (Fin (k + 1)) :=
  Finset.univ.filter fun t => p ∈ I.1 t

lemma layerSupport_nonempty (I : Multichain (P := P) (k := k)) (p : P) :
    (layerSupport I p).Nonempty := by
  refine ⟨Fin.last k, ?_⟩
  simp [layerSupport, I.2.2.2]

/-- The layer in which `p` first appears in the multichain. -/
def layerOf (I : Multichain (P := P) (k := k)) (p : P) : Fin (k + 1) :=
  (layerSupport I p).min' (layerSupport_nonempty I p)

lemma layerOf_mem (I : Multichain (P := P) (k := k)) (p : P) :
    p ∈ I.1 (layerOf I p) := by
  have hmem := Finset.min'_mem (layerSupport I p) (layerSupport_nonempty I p)
  simpa [layerOf, layerSupport] using hmem

lemma layerOf_le_of_mem (I : Multichain (P := P) (k := k)) (p : P)
    (t : Fin (k + 1)) (hp : p ∈ I.1 t) :
    layerOf I p ≤ t := by
  exact Finset.min'_le (layerSupport I p) t (by simp [layerSupport, hp])

/-- Layer differences send a terminal multichain to its first-entry layer assignment. -/
def toPrimeLayers (I : Multichain (P := P) (k := k)) : PrimeLayers (P := P) (k := k) :=
  ⟨fun p => layerOf I p, by
    intro a b hab
    exact layerOf_le_of_mem I a (layerOf I b) (I.2.1 (layerOf I b) hab (layerOf_mem I b))⟩

/-- Cumulative ideals induced by an order-preserving layer assignment. -/
def cumulativeIdeal (L : PrimeLayers (P := P) (k := k)) (t : Fin (k + 1)) : Finset P :=
  Finset.univ.filter fun p => L.1 p ≤ t

/-- Cumulative ideals send a layer assignment to an increasing terminal multichain. -/
def fromPrimeLayers (L : PrimeLayers (P := P) (k := k)) : Multichain (P := P) (k := k) :=
  ⟨fun t => cumulativeIdeal L t, by
    refine ⟨?_, ?_, ?_⟩
    · intro t a b hab hb
      have hb' : L.1 b ≤ t := by simpa [cumulativeIdeal] using hb
      exact by
        simp [cumulativeIdeal, (L.2 hab).trans hb']
    · intro s t hst p hp
      have hp' : L.1 p ≤ s := by simpa [cumulativeIdeal] using hp
      exact by
        simp [cumulativeIdeal, hp'.trans hst]
    · ext p
      simp [cumulativeIdeal, Fin.le_last (L.1 p)]⟩

lemma to_fromPrimeLayers (L : PrimeLayers (P := P) (k := k)) :
    toPrimeLayers (fromPrimeLayers L) = L := by
  apply Subtype.ext
  funext p
  apply le_antisymm
  · exact layerOf_le_of_mem (fromPrimeLayers L) p (L.1 p) (by simp [fromPrimeLayers,
      cumulativeIdeal])
  · have hmem := layerOf_mem (fromPrimeLayers L) p
    simpa [fromPrimeLayers, cumulativeIdeal] using hmem

lemma from_toPrimeLayers (I : Multichain (P := P) (k := k)) :
    fromPrimeLayers (toPrimeLayers I) = I := by
  apply Subtype.ext
  funext t
  ext p
  constructor
  · intro hp
    have hle : layerOf I p ≤ t := by
      simpa [fromPrimeLayers, cumulativeIdeal, toPrimeLayers] using hp
    exact I.2.2.1 hle (layerOf_mem I p)
  · intro hp
    have hle := layerOf_le_of_mem I p t hp
    simp [fromPrimeLayers, cumulativeIdeal, toPrimeLayers, hle]

/-- The layer-difference and cumulative-ideal constructions are inverse bijections. -/
def multichainPrimeLayersEquiv :
    Multichain (P := P) (k := k) ≃ PrimeLayers (P := P) (k := k) where
  toFun := toPrimeLayers
  invFun := fromPrimeLayers
  left_inv := from_toPrimeLayers
  right_inv := to_fromPrimeLayers

end xi_ideal_lattice_multichain_prime_stratification

/-- Paper label:
`prop:xi-ideal-lattice-multichain-prime-stratification`. -/
theorem paper_xi_ideal_lattice_multichain_prime_stratification {P : Type*} [Fintype P]
    [DecidableEq P] [PartialOrder P] (k : ℕ) :
    Fintype.card (xi_ideal_lattice_multichain_prime_stratification_multichains P k) =
      Fintype.card (xi_ideal_lattice_multichain_prime_stratification_prime_layers P k) := by
  exact Fintype.card_congr
    (xi_ideal_lattice_multichain_prime_stratification.multichainPrimeLayersEquiv
      (P := P) (k := k))

end

end Omega.Zeta
