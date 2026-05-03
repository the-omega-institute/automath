import Mathlib

theorem paper_xi_hankel_good_bad_prime_dichotomy (Delta : Int) (p : Nat) (hp : Nat.Prime p) :
    (((Delta : ZMod p) != 0) <-> not ((p : Int) ∣ Delta)) ∧
      (((Delta : ZMod p) = 0) <-> ((p : Int) ∣ Delta)) := by
  have _hp_ne_zero : p ≠ 0 := hp.ne_zero
  have hzero : ((Delta : ZMod p) = 0) ↔ ((p : Int) ∣ Delta) := by
    simpa using (ZMod.intCast_zmod_eq_zero_iff_dvd Delta p)
  constructor
  · constructor
    · intro hne
      have hne_prop : (Delta : ZMod p) ≠ 0 := by
        simpa using hne
      have hnot_prop : ¬ ((p : Int) ∣ Delta) := by
        intro hdvd
        exact hne_prop (hzero.mpr hdvd)
      simpa using hnot_prop
    · intro hnot
      have hnot_prop : ¬ ((p : Int) ∣ Delta) := by
        simpa using hnot
      have hne_prop : (Delta : ZMod p) ≠ 0 := by
        intro hzero_mod
        exact hnot_prop (hzero.mp hzero_mod)
      simpa using hne_prop
  · exact hzero
