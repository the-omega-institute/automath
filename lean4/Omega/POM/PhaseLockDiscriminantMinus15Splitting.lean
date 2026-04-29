import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace Omega.POM

private theorem pom_phase_lock_discriminant_minus15_splitting_natCast_ne_zero_of_prime_ne
    {p n : ℕ} [Fact p.Prime] (hn : n.Prime) (hpn : p ≠ n) :
    (n : ZMod p) ≠ 0 := by
  intro hz
  rw [ZMod.natCast_eq_zero_iff] at hz
  exact hpn ((Nat.prime_dvd_prime_iff_eq Fact.out hn).1 hz)

/-- Paper label: `prop:pom-phase-lock-discriminant-minus15-splitting`. -/
theorem paper_pom_phase_lock_discriminant_minus15_splitting
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    ((∃ z : ZMod p, (2 : ZMod p) * z ^ 2 + z + 2 = 0) ↔
      ∃ y : ZMod p, y ^ 2 = (-15 : ZMod p)) ∧
    ((p = 3 ∨ p = 5) →
      ∃ z : ZMod p,
        (2 : ZMod p) * z ^ 2 + z + 2 = 0 ∧ (4 : ZMod p) * z + 1 = 0) := by
  have h2 : (2 : ZMod p) ≠ 0 :=
    pom_phase_lock_discriminant_minus15_splitting_natCast_ne_zero_of_prime_ne
      (p := p) (n := 2) Nat.prime_two hp2
  have h4 : (4 : ZMod p) ≠ 0 := by
    have hfour_eq : (4 : ZMod p) = (2 : ZMod p) ^ 2 := by norm_num
    rw [hfour_eq]
    exact pow_ne_zero 2 h2
  have h8 : (8 : ZMod p) ≠ 0 := by
    have height_eq : (8 : ZMod p) = (2 : ZMod p) ^ 3 := by norm_num
    rw [height_eq]
    exact pow_ne_zero 3 h2
  refine ⟨?_, ?_⟩
  · constructor
    · rintro ⟨z, hz⟩
      refine ⟨(4 : ZMod p) * z + 1, ?_⟩
      calc
        ((4 : ZMod p) * z + 1) ^ 2 =
            (8 : ZMod p) * ((2 : ZMod p) * z ^ 2 + z + 2) - 15 := by
          ring
        _ = (-15 : ZMod p) := by
          rw [hz]
          ring
    · rintro ⟨y, hy⟩
      let z : ZMod p := (4 : ZMod p)⁻¹ * (y - 1)
      refine ⟨z, ?_⟩
      have hlin : (4 : ZMod p) * z + 1 = y := by
        dsimp [z]
        field_simp [h4]
        ring
      have hzero8 :
          (8 : ZMod p) * ((2 : ZMod p) * z ^ 2 + z + 2) = 0 := by
        calc
          (8 : ZMod p) * ((2 : ZMod p) * z ^ 2 + z + 2) =
              ((4 : ZMod p) * z + 1) ^ 2 + 15 := by
            ring
          _ = y ^ 2 + 15 := by rw [hlin]
          _ = 0 := by
            rw [hy]
            ring
      rcases mul_eq_zero.mp hzero8 with h8zero | hf
      · exact False.elim (h8 h8zero)
      · exact hf
  · intro hp35
    rcases hp35 with hp3 | hp5
    · subst p
      refine ⟨(2 : ZMod 3), ?_, ?_⟩ <;> native_decide +revert
    · subst p
      refine ⟨(1 : ZMod 5), ?_, ?_⟩ <;> native_decide +revert

end Omega.POM
