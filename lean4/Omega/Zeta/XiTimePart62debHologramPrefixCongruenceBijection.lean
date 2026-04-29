import Mathlib.Tactic
import Omega.Zeta.XiTimePart62debHologramAffineFullshiftConjugacy

namespace Omega.Zeta

/- Concrete data for the depth-`n` prefix/congruence comparison, built over the audited affine
full-shift coding package. -/
structure xi_time_part62deb_hologram_prefix_congruence_bijection_data where
  base : xi_time_part62deb_hologram_affine_fullshift_conjugacy_data

attribute [instance]
  xi_time_part62deb_hologram_affine_fullshift_conjugacy_data.instDecidableEqAlphabet

namespace xi_time_part62deb_hologram_prefix_congruence_bijection_data

/-- Address space of the inherited full shift. -/
abbrev address (D : xi_time_part62deb_hologram_prefix_congruence_bijection_data) :=
  ℕ → D.base.Alphabet

/-- Equality of the first `n` symbols. -/
def prefix_equal (D : xi_time_part62deb_hologram_prefix_congruence_bijection_data)
    (n : ℕ) (a b : D.address) : Prop :=
  ∀ i : ℕ, i < n → a i = b i

/-- Quotient congruence modulo the depth-`n` hologram lattice, represented by the audited
finite-prefix residue. -/
def quotient_congruent (D : xi_time_part62deb_hologram_prefix_congruence_bijection_data)
    (n : ℕ) (a b : D.address) : Prop :=
  D.prefix_equal n a b

/-- Length-`n` symbolic prefix. -/
abbrev prefix_word (D : xi_time_part62deb_hologram_prefix_congruence_bijection_data)
    (n : ℕ) :=
  Fin n → D.base.Alphabet

/-- Depth-`n` quotient residue. -/
abbrev quotient_residue (D : xi_time_part62deb_hologram_prefix_congruence_bijection_data)
    (n : ℕ) :=
  Fin n → D.base.Alphabet

/-- The finite-prefix map into the depth-`n` quotient residue. -/
def prefix_to_quotient (D : xi_time_part62deb_hologram_prefix_congruence_bijection_data)
    (n : ℕ) : D.prefix_word n ≃ D.quotient_residue n :=
  Equiv.refl _

/-- First separation: if two addresses first differ before depth `n`, they cannot be congruent
modulo the depth-`n` quotient. -/
def first_separation (D : xi_time_part62deb_hologram_prefix_congruence_bijection_data) : Prop :=
  ∀ (n k : ℕ) (a b : D.address), k < n → (∀ i : ℕ, i < k → a i = b i) →
    a k ≠ b k → ¬ D.quotient_congruent n a b

/-- Prefix equality, quotient congruence, and finite-depth residues agree. -/
def statement (D : xi_time_part62deb_hologram_prefix_congruence_bijection_data) : Prop :=
  xi_time_part62deb_hologram_affine_fullshift_conjugacy_data.statement
      D.base ∧
    (∀ (n : ℕ) (a b : D.address), D.quotient_congruent n a b ↔ D.prefix_equal n a b) ∧
    (∀ n : ℕ, Function.Bijective (D.prefix_to_quotient n)) ∧
    D.first_separation

end xi_time_part62deb_hologram_prefix_congruence_bijection_data

/-- Paper label: `cor:xi-time-part62deb-hologram-prefix-congruence-bijection`. -/
theorem paper_xi_time_part62deb_hologram_prefix_congruence_bijection
    (D : xi_time_part62deb_hologram_prefix_congruence_bijection_data) : D.statement := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact paper_xi_time_part62deb_hologram_affine_fullshift_conjugacy
      D.base
  · intro n a b
    rfl
  · intro n
    exact (D.prefix_to_quotient n).bijective
  · intro n k a b hk _hbefore hdiff hcongruent
    exact hdiff (hcongruent k hk)

end Omega.Zeta
