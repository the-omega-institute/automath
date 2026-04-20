import Mathlib.Data.ZMod.Basic
import Omega.GU.Window6FiberEdgeCouplingDet

namespace Omega.GU

/-- Small nonzero naturals stay nonzero in `ZMod p` when `p` is a different prime. -/
private theorem natCast_ne_zero_of_prime_ne {p n : ℕ} [Fact p.Prime] (hn : n.Prime)
    (hpn : p ≠ n) :
    (n : ZMod p) ≠ 0 := by
  intro hz
  rw [ZMod.natCast_eq_zero_iff] at hz
  exact hpn ((Nat.prime_dvd_prime_iff_eq Fact.out hn).1 hz)

/-- The audited window-6 coupling determinant stays nonzero modulo every prime outside the bad set
`{2, 3, 5, 23}`.  Consequently the coupling matrix is invertible over `𝔽_p`. -/
theorem paper_terminal_window6_fiber_edge_coupling_p_adic_window
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp23 : p ≠ 23) :
    (window6CouplingMatrix.map (Int.castRingHom (ZMod p))).det ≠ 0 := by
  have hdet : (window6CouplingMatrix.map (Int.castRingHom (ZMod p))).det =
      (2 : ZMod p) * 3 * 5 * 23 := by
    classical
    norm_num [window6CouplingMatrix, window6CouplingRowWeight]
  have h2 : (2 : ZMod p) ≠ 0 :=
    natCast_ne_zero_of_prime_ne (p := p) (n := 2) Nat.prime_two hp2
  have h3 : (3 : ZMod p) ≠ 0 :=
    natCast_ne_zero_of_prime_ne (p := p) (n := 3) (by decide : Nat.Prime 3) hp3
  have h5 : (5 : ZMod p) ≠ 0 :=
    natCast_ne_zero_of_prime_ne (p := p) (n := 5) (by decide : Nat.Prime 5) hp5
  have h23 : (23 : ZMod p) ≠ 0 :=
    natCast_ne_zero_of_prime_ne (p := p) (n := 23) (by decide : Nat.Prime 23) hp23
  rw [hdet]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero h2 h3) h5) h23

end Omega.GU
