import Mathlib.Tactic
import Omega.GU.EllipticGatePrimeSpectrumRigidity

namespace Omega.GU

/-- If the gate parameter is perturbed by a `p^K`-sized rational shift, then every one of the
first `N` nonzero even Fourier coefficients changes by a multiple of `p^K`. This packages the
finite-audit `p`-adic blindspot at `m = 1`.
    thm:group-jg-elliptic-gate-padics-blindspot -/
theorem paper_group_jg_elliptic_gate_padics_blindspot
    (c t : ℚ) (p K N : ℕ) (hp : Nat.Prime p) (_hpodd : p ≠ 2) :
    let c' := c + (p : ℚ) ^ K * t
    ∀ n, 0 < n → n ≤ N →
      ∃ z : ℚ,
        ellipticGateLogSpeedFourierCoeffAtMultiple c' n -
            ellipticGateLogSpeedFourierCoeffAtMultiple c n =
          ((p : ℚ) ^ K) * z := by
  intro c' n hn _hnN
  have hp0 : (p : ℚ) ≠ 0 := by
    exact_mod_cast hp.ne_zero
  have htwo : (2 : ℚ) ≠ 0 := by norm_num
  let s : ℚ := Finset.sum (Finset.range n) (fun i => c' ^ i * c ^ (n - 1 - i))
  refine ⟨-(t * s) / (2 * n), ?_⟩
  have hc' : ellipticGateLogSpeedFourierCoeffAtMultiple c' n = -(c' ^ n) / (2 * n) :=
    ellipticGateLogSpeedFourierCoeffAtMultiple_eq c' hn
  have hc : ellipticGateLogSpeedFourierCoeffAtMultiple c n = -(c ^ n) / (2 * n) :=
    ellipticGateLogSpeedFourierCoeffAtMultiple_eq c hn
  have hfactor : (c' - c) * s = c' ^ n - c ^ n := by
    dsimp [s]
    simpa [mul_comm, mul_left_comm, mul_assoc] using (Commute.all c' c).mul_geom_sum₂ n
  have hshift : c' - c = (p : ℚ) ^ K * t := by
    dsimp [c']
    ring
  calc
    ellipticGateLogSpeedFourierCoeffAtMultiple c' n -
        ellipticGateLogSpeedFourierCoeffAtMultiple c n
        = -(c' ^ n) / (2 * n) - (-(c ^ n) / (2 * n)) := by rw [hc', hc]
    _ = -((c' ^ n - c ^ n) / (2 * n)) := by ring
    _ = -(((c' - c) * s) / (2 * n)) := by rw [hfactor]
    _ = -((((p : ℚ) ^ K) * t * s) / (2 * n)) := by rw [hshift]
    _ = ((p : ℚ) ^ K) * (-(t * s) / (2 * n)) := by
      field_simp [hp0, htwo]

end Omega.GU
