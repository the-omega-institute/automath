import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic
import Omega.DerivedConsequences.DerivedWindow6HalfblockRecoversLucasDivisorLattice

namespace Omega.DerivedConsequences

open scoped BigOperators

noncomputable section

/-- Concrete fixed-conductor data for the window-`6` halfblock blindness bound. The normalized
Ramanujan shadow is controlled conductorwise by the Euler-totient envelope over a finite set of
conductors, and an additional Binet-style decay parameter bounds the reciprocal Lucas factor. -/
structure derived_window6_halfblock_fixed_conductor_blindness_data where
  factorizationData : derived_window6_halfblock_recovers_lucas_divisor_lattice_data
  conductors : Finset ℕ
  hconductors_nonempty : conductors.Nonempty
  normalizedShadow : ℕ → ℝ
  decayScale : ℝ
  ramanujan_shadow_bound :
    ∀ q ∈ conductors,
      |normalizedShadow q| ≤
        (Nat.totient q : ℝ) /
          (((Omega.Zeta.lucasNum
              (derived_window6_halfblock_recovers_lucas_divisor_lattice_level factorizationData) :
                ℤ) : ℝ))
  lucas_inverse_decay_bound :
    (1 : ℝ) /
        (((Omega.Zeta.lucasNum
            (derived_window6_halfblock_recovers_lucas_divisor_lattice_level factorizationData) :
              ℤ) : ℝ)) ≤
      decayScale

/-- The fixed conductor envelope `max_{q ∈ Q} φ(q)`. -/
noncomputable def derived_window6_halfblock_fixed_conductor_blindness_conductorEnvelope
    (D : derived_window6_halfblock_fixed_conductor_blindness_data) : ℕ :=
  (D.conductors.image Nat.totient).max' <| by
    rcases D.hconductors_nonempty with ⟨q, hq⟩
    exact ⟨Nat.totient q, Finset.mem_image.mpr ⟨q, hq, rfl⟩⟩

/-- The finite maximum of the normalized Ramanujan-shadow magnitudes over the conductor set. -/
noncomputable def derived_window6_halfblock_fixed_conductor_blindness_shadowMax
    (D : derived_window6_halfblock_fixed_conductor_blindness_data) : ℝ :=
  (D.conductors.image fun q => |D.normalizedShadow q|).max' <| by
    rcases D.hconductors_nonempty with ⟨q, hq⟩
    exact ⟨|D.normalizedShadow q|, Finset.mem_image.mpr ⟨q, hq, rfl⟩⟩

/-- The Lucas denominator carried by the halfblock factorization package. -/
def derived_window6_halfblock_fixed_conductor_blindness_lucasDenominator
    (D : derived_window6_halfblock_fixed_conductor_blindness_data) : ℝ :=
  (((Omega.Zeta.lucasNum
      (derived_window6_halfblock_recovers_lucas_divisor_lattice_level D.factorizationData) :
        ℤ) : ℝ))

/-- Paper-facing fixed-conductor blindness package: the divisor-lattice factorization persists, the
finite maximum of the normalized Ramanujan shadows is bounded by the fixed conductor envelope over
the Lucas denominator, and the latter is in turn dominated by the explicit Binet-style decay
scale. -/
def derived_window6_halfblock_fixed_conductor_blindness_statement
    (D : derived_window6_halfblock_fixed_conductor_blindness_data) : Prop :=
  derived_window6_halfblock_recovers_lucas_divisor_lattice_statement D.factorizationData ∧
    derived_window6_halfblock_fixed_conductor_blindness_shadowMax D ≤
      (derived_window6_halfblock_fixed_conductor_blindness_conductorEnvelope D : ℝ) /
        derived_window6_halfblock_fixed_conductor_blindness_lucasDenominator D ∧
    derived_window6_halfblock_fixed_conductor_blindness_shadowMax D ≤
      (derived_window6_halfblock_fixed_conductor_blindness_conductorEnvelope D : ℝ) * D.decayScale

/-- Paper label: `thm:derived-window6-halfblock-fixed-conductor-blindness`. -/
theorem paper_derived_window6_halfblock_fixed_conductor_blindness
    (D : derived_window6_halfblock_fixed_conductor_blindness_data) :
    derived_window6_halfblock_fixed_conductor_blindness_statement D := by
  classical
  have hFactor :=
    paper_derived_window6_halfblock_recovers_lucas_divisor_lattice D.factorizationData
  have hLucas_pos_int :
      0 <
        Omega.Zeta.lucasNum
          (derived_window6_halfblock_recovers_lucas_divisor_lattice_level D.factorizationData) :=
    Omega.Zeta.lucasNum_pos
      (derived_window6_halfblock_recovers_lucas_divisor_lattice_level D.factorizationData)
  have hLucas_pos :
      0 < derived_window6_halfblock_fixed_conductor_blindness_lucasDenominator D := by
    unfold derived_window6_halfblock_fixed_conductor_blindness_lucasDenominator
    exact_mod_cast hLucas_pos_int
  have hEnvelope_nonempty :
      (D.conductors.image Nat.totient).Nonempty := by
    rcases D.hconductors_nonempty with ⟨q, hq⟩
    exact ⟨Nat.totient q, Finset.mem_image.mpr ⟨q, hq, rfl⟩⟩
  have hShadow_nonempty :
      (D.conductors.image fun q => |D.normalizedShadow q|).Nonempty := by
    rcases D.hconductors_nonempty with ⟨q, hq⟩
    exact ⟨|D.normalizedShadow q|, Finset.mem_image.mpr ⟨q, hq, rfl⟩⟩
  have hShadowEnvelope :
      derived_window6_halfblock_fixed_conductor_blindness_shadowMax D ≤
        (derived_window6_halfblock_fixed_conductor_blindness_conductorEnvelope D : ℝ) /
          derived_window6_halfblock_fixed_conductor_blindness_lucasDenominator D := by
    unfold derived_window6_halfblock_fixed_conductor_blindness_shadowMax
      derived_window6_halfblock_fixed_conductor_blindness_conductorEnvelope
      derived_window6_halfblock_fixed_conductor_blindness_lucasDenominator
    rcases Finset.mem_image.mp
        (Finset.max'_mem (D.conductors.image fun q => |D.normalizedShadow q|) hShadow_nonempty) with
      ⟨q, hq, hqmax⟩
    have hbound_q := D.ramanujan_shadow_bound q hq
    have htotient_le :
        Nat.totient q ≤ (D.conductors.image Nat.totient).max' hEnvelope_nonempty := by
      exact Finset.le_max' (D.conductors.image Nat.totient) (Nat.totient q)
        (Finset.mem_image.mpr ⟨q, hq, rfl⟩)
    have htotient_le_real :
        (Nat.totient q : ℝ) ≤ ((D.conductors.image Nat.totient).max' hEnvelope_nonempty : ℝ) := by
      exact_mod_cast htotient_le
    rw [← hqmax]
    exact le_trans hbound_q (div_le_div_of_nonneg_right htotient_le_real hLucas_pos.le)
  have hDecay :
      (derived_window6_halfblock_fixed_conductor_blindness_conductorEnvelope D : ℝ) /
          derived_window6_halfblock_fixed_conductor_blindness_lucasDenominator D ≤
        (derived_window6_halfblock_fixed_conductor_blindness_conductorEnvelope D : ℝ) *
          D.decayScale := by
    have hmul :=
      mul_le_mul_of_nonneg_left D.lucas_inverse_decay_bound
        (show
          0 ≤ (derived_window6_halfblock_fixed_conductor_blindness_conductorEnvelope D : ℝ) by
            positivity)
    simpa [derived_window6_halfblock_fixed_conductor_blindness_lucasDenominator, div_eq_mul_inv,
      mul_assoc, mul_left_comm, mul_comm] using hmul
  exact ⟨hFactor, hShadowEnvelope, le_trans hShadowEnvelope hDecay⟩

end

end Omega.DerivedConsequences
