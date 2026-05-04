import Mathlib.Tactic

namespace Omega.Zeta

universe u

/-- Concrete data for the strict self-similar decomposition of a finite holographic address image. -/
structure xi_time_part62ca_holographic_address_strict_selfsimilarity_data where
  Alphabet : Type u
  finiteAlphabet : Fintype Alphabet
  decidableAlphabet : DecidableEq Alphabet
  base : ℕ
  base_pos : 0 < base
  code : Alphabet → Fin base
  code_injective : Function.Injective code

attribute [local instance] xi_time_part62ca_holographic_address_strict_selfsimilarity_data.finiteAlphabet
attribute [local instance] xi_time_part62ca_holographic_address_strict_selfsimilarity_data.decidableAlphabet

/-- The encoded `base`-adic stream attached to an event stream. -/
def xi_time_part62ca_holographic_address_strict_selfsimilarity_address
    (D : xi_time_part62ca_holographic_address_strict_selfsimilarity_data)
    (e : ℕ → D.Alphabet) : ℕ → Fin D.base :=
  fun t => D.code (e t)

/-- The holographic address image as a concrete set of encoded digit streams. -/
def xi_time_part62ca_holographic_address_strict_selfsimilarity_image
    (D : xi_time_part62ca_holographic_address_strict_selfsimilarity_data) :
    Set (ℕ → Fin D.base) :=
  Set.range (xi_time_part62ca_holographic_address_strict_selfsimilarity_address D)

/-- The block with prescribed first encoded digit. -/
def xi_time_part62ca_holographic_address_strict_selfsimilarity_block
    (D : xi_time_part62ca_holographic_address_strict_selfsimilarity_data) (a : Fin D.base) :
    Set (ℕ → Fin D.base) :=
  {x | x ∈ xi_time_part62ca_holographic_address_strict_selfsimilarity_image D ∧ x 0 = a}

/-- Tail-shift presentation of a first-symbol cylinder. -/
def xi_time_part62ca_holographic_address_strict_selfsimilarity_scaledTail
    (D : xi_time_part62ca_holographic_address_strict_selfsimilarity_data) (a : Fin D.base) :
    Set (ℕ → Fin D.base) :=
  {x | ∃ e : ℕ → D.Alphabet,
      D.code (e 0) = a ∧
        x = fun t => Nat.casesOn t a
          (fun s => xi_time_part62ca_holographic_address_strict_selfsimilarity_address D e (s + 1))}

/-- The quotient/coset membership predicate recording the first `base`-adic digit. -/
def xi_time_part62ca_holographic_address_strict_selfsimilarity_coset
    (D : xi_time_part62ca_holographic_address_strict_selfsimilarity_data) (a : Fin D.base) :
    Set (ℕ → Fin D.base) :=
  {x | x 0 = a}

/-- Concrete statement: the address image is the disjoint union of its first-digit cylinders, and
each cylinder is exactly image membership plus one quotient/coset condition. -/
def xi_time_part62ca_holographic_address_strict_selfsimilarity_statement
    (D : xi_time_part62ca_holographic_address_strict_selfsimilarity_data) : Prop :=
  (xi_time_part62ca_holographic_address_strict_selfsimilarity_image D =
      {x | ∃ a, a ∈ Set.range D.code ∧
        x ∈ xi_time_part62ca_holographic_address_strict_selfsimilarity_block D a}) ∧
    (∀ a ∈ Set.range D.code,
      xi_time_part62ca_holographic_address_strict_selfsimilarity_block D a =
        xi_time_part62ca_holographic_address_strict_selfsimilarity_scaledTail D a) ∧
    (∀ a ∈ Set.range D.code, ∀ b ∈ Set.range D.code, a ≠ b →
      Disjoint
        (xi_time_part62ca_holographic_address_strict_selfsimilarity_block D a)
        (xi_time_part62ca_holographic_address_strict_selfsimilarity_block D b)) ∧
    (∀ a ∈ Set.range D.code,
      xi_time_part62ca_holographic_address_strict_selfsimilarity_block D a =
        xi_time_part62ca_holographic_address_strict_selfsimilarity_image D ∩
          xi_time_part62ca_holographic_address_strict_selfsimilarity_coset D a)

/-- Paper label:
`thm:xi-time-part62ca-holographic-address-strict-selfsimilarity`. -/
theorem paper_xi_time_part62ca_holographic_address_strict_selfsimilarity
    (D : xi_time_part62ca_holographic_address_strict_selfsimilarity_data) :
    xi_time_part62ca_holographic_address_strict_selfsimilarity_statement D := by
  classical
  unfold xi_time_part62ca_holographic_address_strict_selfsimilarity_statement
  constructor
  · ext x
    constructor
    · rintro ⟨e, rfl⟩
      refine ⟨D.code (e 0), ⟨e 0, rfl⟩, ?_⟩
      exact ⟨⟨e, rfl⟩, rfl⟩
    · rintro ⟨a, _ha, hx⟩
      exact hx.1
  constructor
  · intro a ha
    ext x
    constructor
    · rintro ⟨⟨e, rfl⟩, hfirst⟩
      refine ⟨e, hfirst, ?_⟩
      funext t
      cases t
      · exact hfirst
      · rfl
    · rintro ⟨e, hfirst, rfl⟩
      refine ⟨?_, ?_⟩
      · refine ⟨e, ?_⟩
        funext t
        cases t
        · exact hfirst
        · rfl
      · rfl
  constructor
  · intro a ha b hb hab
    rw [Set.disjoint_left]
    intro x hx hy
    exact hab (hx.2.symm.trans hy.2)
  · intro a ha
    ext x
    rfl

end Omega.Zeta
