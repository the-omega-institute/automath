import Omega.Zeta.SmithEntropyMinDepth

namespace Omega.Zeta

/-- Exact multiplicities are the discrete derivative of the Smith tail counts. -/
theorem smithMultiplicity_eq_delta_sub (s : Multiset ℕ) (k : ℕ) :
    (s.filter fun v => v = k).card = smithDelta s k - smithDelta s (k + 1) := by
  unfold smithDelta
  induction s using Multiset.induction with
  | empty =>
      simp
  | cons v t ih =>
      by_cases hvk : v = k
      · subst v
        have hsub1 : t.filter (fun x => k < x) ≤ t.filter (fun x => k + 1 ≤ x) :=
          Multiset.monotone_filter_right t (by intro x hx; omega)
        have hsub2 : t.filter (fun x => k + 1 ≤ x) ≤ t.filter (fun x => k < x) :=
          Multiset.monotone_filter_right t (by intro x hx; omega)
        have hgt : (t.filter fun x => k < x).card = (t.filter fun x => k + 1 ≤ x).card :=
          le_antisymm (Multiset.card_le_card hsub1) (Multiset.card_le_card hsub2)
        have hle : (t.filter fun x => k + 1 ≤ x).card ≤ (t.filter fun x => k ≤ x).card :=
          Multiset.card_le_card <| Multiset.monotone_filter_right t (by intro x hx; omega)
        simp [ih]
        rw [hgt]
        omega
      · by_cases hkv : k + 1 ≤ v
        · have hk : k ≤ v := by omega
          have hklt : k < v := by omega
          simp [hvk, hk, hklt, ih, Nat.succ_sub_succ_eq_sub]
        · have hk : ¬k ≤ v := by omega
          have hklt : ¬k < v := by omega
          simp [hvk, hk, hklt, ih]

/-- Paper package: the Smith entropy increments recover the multiplicity table of the p-adic
invariants.  This is the multiset form of the inversion formula in the paper. -/
theorem paper_xi_smith_entropy_inverts_vp_invariants (s : Multiset ℕ) :
    (∀ k : ℕ, smithEntropy s (k + 1) = smithEntropy s k + smithDelta s (k + 1)) ∧
      (∀ k : ℕ, (s.filter fun v => v = k).card = smithDelta s k - smithDelta s (k + 1)) := by
  exact ⟨smithEntropy_succ_eq_add_delta s, smithMultiplicity_eq_delta_sub s⟩

end Omega.Zeta
