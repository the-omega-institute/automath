import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

/-- A concrete `p`-adic Cauchy criterion for the base sequence `a_{p^k}(1)`. -/
def baseSequenceConvergesPadically {U : Type*} [Monoid U] (p : ℕ) (a : U → ℕ → ℤ) : Prop :=
  ∀ s r, s ≤ r → ((p ^ s : ℤ) ∣ a 1 r - a 1 s)

/-- Every `p`-th root-of-unity slice is congruent modulo `p^(k-1)` to the same base-stage
approximation. This is the finite-level avatar of convergence to the common `p`-adic limit. -/
def rootOfUnitySlicesShareCommonLimit {U : Type*} [Monoid U] (p : ℕ) (a : U → ℕ → ℤ) : Prop :=
  ∀ u, u ^ p = 1 → ∀ k, 1 ≤ k → ((p ^ (k - 1) : ℤ) ∣ a u k - a 1 (k - 1))

/-- Paper label: `thm:witt-root-of-unity-common-padic-limit`. If the base sequence satisfies the
successive Dwork congruences at `u = 1`, and every `p`-th root-of-unity slice is uniformly
congruent to the previous base level modulo `p^k`, then the base sequence is `p`-adically Cauchy
and every root-of-unity slice agrees with the same limit modulo `p^(k-1)`. -/
theorem paper_witt_root_of_unity_common_padic_limit
    {U : Type*} [Monoid U] (p : ℕ) (_hp : Nat.Prime p) (a : U → ℕ → ℤ)
    (hbase : ∀ k, 1 ≤ k → ((p ^ k : ℤ) ∣ a 1 k - a 1 (k - 1)))
    (hroot : ∀ u, u ^ p = 1 → ∀ k, 1 ≤ k → ((p ^ k : ℤ) ∣ a u k - a 1 (k - 1))) :
    baseSequenceConvergesPadically p a ∧ rootOfUnitySlicesShareCommonLimit p a := by
  refine ⟨?_, ?_⟩
  · intro s r hsr
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hsr
    induction n generalizing s with
    | zero =>
        simp
    | succ n ih =>
        have hstepStrong : ((p ^ (s + n + 1) : ℤ) ∣ a 1 (s + n + 1) - a 1 (s + n)) := by
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
            hbase (s + n + 1) (by omega)
        have hpowNat : p ^ s ∣ p ^ (s + n + 1) := by
          exact pow_dvd_pow p (by omega)
        have hpowInt : ((p ^ s : ℤ) ∣ (p ^ (s + n + 1) : ℤ)) := by
          rcases hpowNat with ⟨t, ht⟩
          refine ⟨(t : ℤ), ?_⟩
          exact_mod_cast ht
        have hstepWeak : ((p ^ s : ℤ) ∣ a 1 (s + n + 1) - a 1 (s + n)) :=
          dvd_trans hpowInt hstepStrong
        have hsplit :
            a 1 (s + (n + 1)) - a 1 s =
              (a 1 (s + (n + 1)) - a 1 (s + n)) + (a 1 (s + n) - a 1 s) := by
          ring
        rw [hsplit]
        exact Int.dvd_add hstepWeak (ih s (by omega))
  · intro u hu k hk
    have hstrong : ((p ^ k : ℤ) ∣ a u k - a 1 (k - 1)) := hroot u hu k hk
    have hpowNat : p ^ (k - 1) ∣ p ^ k := by
      exact pow_dvd_pow p (Nat.sub_le k 1)
    have hpowInt : ((p ^ (k - 1) : ℤ) ∣ (p ^ k : ℤ)) := by
      rcases hpowNat with ⟨t, ht⟩
      refine ⟨(t : ℤ), ?_⟩
      exact_mod_cast ht
    exact dvd_trans hpowInt hstrong

end Omega.SyncKernelWeighted
