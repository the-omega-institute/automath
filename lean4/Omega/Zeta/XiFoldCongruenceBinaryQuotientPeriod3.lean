import Mathlib.Tactic

namespace Omega.Zeta

/-- The specialized dyadic depth readout attached to the binary quotient seed. -/
def xi_fold_congruence_binary_quotient_period3_v2 (n : ℕ) : ℕ :=
  if 2 ∣ n then 1 else 0

/-- Paper label: `cor:xi-fold-congruence-binary-quotient-period3`. -/
theorem paper_xi_fold_congruence_binary_quotient_period3
    (F v2 : ℕ → ℕ) (hasBinaryQuotient : ℕ → Prop) (hF1 : F 1 = 1) (hF2 : F 2 = 1)
    (hF3 : F 3 = 0) (hperiod : ∀ n, F (n + 3) % 2 = F n % 2)
    (hquot : ∀ m, hasBinaryQuotient m ↔ 2 ∣ F (m + 2))
    (hdepth : ∀ m, v2 m = xi_fold_congruence_binary_quotient_period3_v2 (F (m + 2))) :
    (∀ m, hasBinaryQuotient m ↔ 3 ∣ (m + 2)) ∧
      (∀ m, v2 m = xi_fold_congruence_binary_quotient_period3_v2 (F (m + 2))) := by
  have hpattern :
      ∀ k, F (3 * k + 1) % 2 = 1 ∧ F (3 * k + 2) % 2 = 1 ∧
        F (3 * k + 3) % 2 = 0 := by
    intro k
    induction k with
    | zero =>
        simp [hF1, hF2, hF3]
    | succ k ih =>
        refine ⟨?_, ?_, ?_⟩
        · have hshift := hperiod (3 * k + 1)
          have harg : 3 * (k + 1) + 1 = (3 * k + 1) + 3 := by omega
          rw [harg, hshift, ih.1]
        · have hshift := hperiod (3 * k + 2)
          have harg : 3 * (k + 1) + 2 = (3 * k + 2) + 3 := by omega
          rw [harg, hshift, ih.2.1]
        · have hshift := hperiod (3 * k + 3)
          have harg : 3 * (k + 1) + 3 = (3 * k + 3) + 3 := by omega
          rw [harg, hshift, ih.2.2]
  refine ⟨?_, hdepth⟩
  intro m
  have hdecomp : m % 3 + 3 * (m / 3) = m := Nat.mod_add_div m 3
  have hlt : m % 3 < 3 := Nat.mod_lt m (by decide)
  have hcases : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
  rw [hquot m]
  rcases hcases with h0 | h1 | h2
  · have hm : m = 3 * (m / 3) := by omega
    have harg : m + 2 = 3 * (m / 3) + 2 := by omega
    have hodd : F (m + 2) % 2 = 1 := by
      rw [harg]
      exact (hpattern (m / 3)).2.1
    have hnotTwo : ¬ 2 ∣ F (m + 2) := by
      intro htwo
      have hzero : F (m + 2) % 2 = 0 := (Nat.dvd_iff_mod_eq_zero).mp htwo
      omega
    have hnotThree : ¬ 3 ∣ m + 2 := by
      intro hthree
      rcases hthree with ⟨q, hq⟩
      omega
    exact ⟨fun htwo => False.elim (hnotTwo htwo), fun hthree => False.elim (hnotThree hthree)⟩
  · have hm : m = 3 * (m / 3) + 1 := by omega
    have harg : m + 2 = 3 * (m / 3) + 3 := by omega
    have heven : F (m + 2) % 2 = 0 := by
      rw [harg]
      exact (hpattern (m / 3)).2.2
    have htwo : 2 ∣ F (m + 2) := (Nat.dvd_iff_mod_eq_zero).mpr heven
    have hthree : 3 ∣ m + 2 := by
      refine ⟨m / 3 + 1, ?_⟩
      omega
    exact ⟨fun _ => hthree, fun _ => htwo⟩
  · have hm : m = 3 * (m / 3) + 2 := by omega
    have harg : m + 2 = 3 * (m / 3 + 1) + 1 := by omega
    have hodd : F (m + 2) % 2 = 1 := by
      rw [harg]
      exact (hpattern (m / 3 + 1)).1
    have hnotTwo : ¬ 2 ∣ F (m + 2) := by
      intro htwo
      have hzero : F (m + 2) % 2 = 0 := (Nat.dvd_iff_mod_eq_zero).mp htwo
      omega
    have hnotThree : ¬ 3 ∣ m + 2 := by
      intro hthree
      rcases hthree with ⟨q, hq⟩
      omega
    exact ⟨fun htwo => False.elim (hnotTwo htwo), fun hthree => False.elim (hnotThree hthree)⟩

end Omega.Zeta
