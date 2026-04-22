import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

/-- Paper label: `prop:witt-unit-root-limit`. Successive congruences modulo `p^k` telescope to a
`p`-adic Cauchy criterion at every fixed point `u` of Frobenius. -/
theorem paper_witt_unit_root_limit {U : Type} [Monoid U] (p : Nat) (_hp : Nat.Prime p)
    (a : U → Nat → Int)
    (hstep : ∀ u, u ^ p = u → ∀ k, 1 ≤ k → ((p ^ k : Int) ∣ a u k - a u (k - 1))) :
    ∀ u, u ^ p = u → ∀ s r, s ≤ r → ((p ^ (s + 1) : Int) ∣ a u r - a u s) := by
  intro u hu s r hsr
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hsr
  induction n generalizing s with
  | zero =>
      simp
  | succ n ih =>
      have hstepStrong : ((p ^ (s + n + 1) : Int) ∣ a u (s + n + 1) - a u (s + n)) := by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hstep u hu (s + n + 1) (by omega)
      have hpowNat : p ^ (s + 1) ∣ p ^ (s + n + 1) := by
        exact pow_dvd_pow p (by omega)
      have hpowInt : ((p ^ (s + 1) : Int) ∣ (p ^ (s + n + 1) : Int)) := by
        rcases hpowNat with ⟨t, ht⟩
        refine ⟨(t : Int), ?_⟩
        exact_mod_cast ht
      have hstepWeak : ((p ^ (s + 1) : Int) ∣ a u (s + n + 1) - a u (s + n)) :=
        dvd_trans hpowInt hstepStrong
      have hsplit :
          a u (s + (n + 1)) - a u s =
            (a u (s + (n + 1)) - a u (s + n)) + (a u (s + n) - a u s) := by
        ring
      rw [hsplit]
      exact Int.dvd_add hstepWeak (ih s (by omega))

end Omega.SyncKernelWeighted
