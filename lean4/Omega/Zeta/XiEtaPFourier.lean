import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Zeta

noncomputable section

/-- The sign contributed by the distinguished `p`-th root of `-1`. -/
def xi_eta_p_fourier_sign (p : ℕ) (n : ℤ) : ℂ :=
  (-1 : ℂ) ^ (n / (p : ℤ))

/-- The normalized Fourier average over the `p` phase classes. The additive character packages the
geometric sum over the `p` roots of unity, while `xi_eta_p_fourier_sign` records the extra
half-step phase needed to pass from `z^p = 1` to `z^p = -1`. -/
def xi_eta_p_fourier_average (p : ℕ) (n : ℤ) : ℂ :=
  if hp : p = 0 then
    0
  else
    letI : NeZero p := ⟨hp⟩
    xi_eta_p_fourier_sign p n *
      (((p : ℂ)⁻¹) * ∑ x : ZMod p, ZMod.stdAddChar (N := p) (x * (n : ZMod p)))

/-- The `p`-point Fourier average is the sign factor when `p ∣ n` and vanishes otherwise. -/
def xi_eta_p_fourier_statement (p : ℕ) (n : ℤ) : Prop :=
  xi_eta_p_fourier_average p n =
    if p = 0 then
      0
    else
      if (p : ℤ) ∣ n then xi_eta_p_fourier_sign p n else 0

theorem paper_xi_eta_p_fourier (p : ℕ) (n : ℤ) : xi_eta_p_fourier_statement p n := by
  by_cases hp : p = 0
  · simp [xi_eta_p_fourier_statement, xi_eta_p_fourier_average, hp]
  · letI : NeZero p := ⟨hp⟩
    have hsum :=
      AddChar.sum_mulShift (R := ZMod p) (R' := ℂ) (ψ := ZMod.stdAddChar (N := p))
        (b := (n : ZMod p)) (ZMod.isPrimitive_stdAddChar p)
    have hp_nat_pos : 0 < p := Nat.pos_iff_ne_zero.mpr hp
    have hpℂ : (p : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hp_nat_pos)
    have hzero_iff : (n : ZMod p) = 0 ↔ (p : ℤ) ∣ n := by
      simpa using (ZMod.intCast_zmod_eq_zero_iff_dvd n p)
    by_cases hdiv : (p : ℤ) ∣ n
    · have hz : (n : ZMod p) = 0 := hzero_iff.mpr hdiv
      simp [xi_eta_p_fourier_statement, xi_eta_p_fourier_average, hp, hdiv, hz,
        hpℂ, xi_eta_p_fourier_sign]
    · have hz : (n : ZMod p) ≠ 0 := by
        exact fun hz => hdiv (hzero_iff.mp hz)
      simp [xi_eta_p_fourier_statement, xi_eta_p_fourier_average, hp, hdiv, hz, hsum,
        xi_eta_p_fourier_sign]

end

end Omega.Zeta
