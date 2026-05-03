import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete divisor-lattice syndrome layer: multiples of `D`.  Inclusion of these layers is
the order opposite to divisibility of the generators. -/
def xi_time_part62af_hankel_gap_divisor_lattice_layer (D : ℕ) : Set ℕ :=
  {x | D ∣ x}

/-- Rank of the divisor ideal `(D)/(R)` in the degree model. -/
def xi_time_part62af_hankel_gap_divisor_lattice_idealRank (Δ degD : ℕ) : ℕ :=
  Δ - degD

/-- Rank of the quotient by the divisor ideal in the degree model. -/
def xi_time_part62af_hankel_gap_divisor_lattice_quotientRank (_Δ degD : ℕ) : ℕ :=
  degD

/-- Concrete divisor-lattice statement: divisibility is reversed by layer inclusion, lcm gives
intersection, and the two complementary rank formulas add to the ambient degree. -/
def xi_time_part62af_hankel_gap_divisor_lattice_statement : Prop :=
  (∀ D₁ D₂ : ℕ,
      D₁ ∣ D₂ ↔
        xi_time_part62af_hankel_gap_divisor_lattice_layer D₂ ⊆
          xi_time_part62af_hankel_gap_divisor_lattice_layer D₁) ∧
    (∀ D₁ D₂ : ℕ,
      xi_time_part62af_hankel_gap_divisor_lattice_layer D₁ ∩
          xi_time_part62af_hankel_gap_divisor_lattice_layer D₂ =
        xi_time_part62af_hankel_gap_divisor_lattice_layer (Nat.lcm D₁ D₂)) ∧
    (∀ Δ degD : ℕ, degD ≤ Δ →
      xi_time_part62af_hankel_gap_divisor_lattice_idealRank Δ degD = Δ - degD ∧
        xi_time_part62af_hankel_gap_divisor_lattice_quotientRank Δ degD = degD ∧
          xi_time_part62af_hankel_gap_divisor_lattice_idealRank Δ degD +
              xi_time_part62af_hankel_gap_divisor_lattice_quotientRank Δ degD =
            Δ)

/-- Paper label: `thm:xi-time-part62af-hankel-gap-divisor-lattice`. -/
theorem paper_xi_time_part62af_hankel_gap_divisor_lattice :
    xi_time_part62af_hankel_gap_divisor_lattice_statement := by
  refine ⟨?_, ?_, ?_⟩
  · intro D₁ D₂
    constructor
    · intro hdiv x hx
      exact dvd_trans hdiv hx
    · intro hsubset
      exact hsubset (dvd_refl D₂)
  · intro D₁ D₂
    ext x
    simpa [xi_time_part62af_hankel_gap_divisor_lattice_layer, Set.mem_inter_iff] using
      (lcm_dvd_iff : Nat.lcm D₁ D₂ ∣ x ↔ D₁ ∣ x ∧ D₂ ∣ x).symm
  · intro Δ degD hdeg
    refine ⟨rfl, rfl, ?_⟩
    simp [xi_time_part62af_hankel_gap_divisor_lattice_idealRank,
      xi_time_part62af_hankel_gap_divisor_lattice_quotientRank, Nat.sub_add_cancel hdeg]

end Omega.Zeta
