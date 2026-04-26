import Mathlib
import Omega.Conclusion.ZGDensityExactInhomogeneousMarkov

namespace Omega.Conclusion

/-- The dyadic address base `B = 2^L`. -/
def addressBase (L : ℕ) : ℕ :=
  2 ^ L

/-- Finite prefix value of a digit string in base `2^L`. -/
def addressValue (L : ℕ) (digits : List ℕ) : ℕ :=
  Nat.ofDigits (addressBase L) digits

lemma addressBase_gt_one {L : ℕ} (hL : 0 < L) : 1 < addressBase L := by
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hL) with ⟨k, rfl⟩
  have hpow : 1 ≤ 2 ^ k := Nat.succ_le_of_lt (by positivity)
  have htwo : 2 ≤ 2 ^ k * 2 := by
    simpa using Nat.mul_le_mul_right 2 hpow
  have htwo' : 1 < 2 ^ k * 2 := lt_of_lt_of_le (by norm_num) htwo
  simpa [addressBase, pow_succ, Nat.mul_comm] using htwo'

lemma addressValue_prefix_mod (L : ℕ) (pre tail : List ℕ) :
    addressValue L (pre ++ tail) ≡ addressValue L pre [MOD addressBase L ^ pre.length] := by
  have hle : addressValue L pre ≤ addressValue L (pre ++ tail) := by
    simp [addressValue, Nat.ofDigits_append]
  have hmod : addressValue L pre ≡ addressValue L (pre ++ tail) [MOD addressBase L ^ pre.length] := by
    rw [Nat.modEq_iff_dvd' hle]
    refine ⟨addressValue L tail, ?_⟩
    simp [addressValue, Nat.ofDigits_append]
  exact hmod.symm

lemma addressValue_injective_of_digits_lt_base {L M : ℕ} (hL : 0 < L) (hBM : M < addressBase L)
    {x y : List ℕ} (hlen : x.length = y.length)
    (hx : ∀ d ∈ x, d ≤ M) (hy : ∀ d ∈ y, d ≤ M) :
    addressValue L x = addressValue L y → x = y := by
  intro hxy
  apply Nat.ofDigits_inj_of_len_eq (addressBase_gt_one hL) hlen
  · intro d hd
    exact lt_of_le_of_lt (hx d hd) hBM
  · intro d hd
    exact lt_of_le_of_lt (hy d hd) hBM
  · simpa [addressValue] using hxy

/-- Paper-facing address-filtration package: appending a tail changes the address only by a
multiple of `B^n`, finite prefixes are unique when all digits lie below the base, and the
existing ZG density theorem can be imported unchanged into the same address model.
    cor:conclusion-time-as-address-resolution-filtration -/
theorem paper_conclusion_time_as_address_resolution_filtration
    (L M : ℕ) (hL : 0 < L) (hBM : M < addressBase L)
    (pre tail : List ℕ) (w : ZGInhomogeneousMarkovWitness) :
    addressValue L (pre ++ tail) ≡ addressValue L pre [MOD addressBase L ^ pre.length] ∧
      (∀ {x y : List ℕ}, x.length = y.length →
        (∀ d ∈ x, d ≤ M) → (∀ d ∈ y, d ≤ M) →
          addressValue L x = addressValue L y → x = y) ∧
      ((∀ n,
        w.condProb n true = 0 ∧
          w.condProb n false =
            w.B (n + 1) / (w.p (n + 1) * w.A (n + 1) + w.B (n + 1))) ∧
        (∀ n,
          w.B n / w.A n =
            w.p (n + 1) / (w.p (n + 1) + w.B (n + 1) / w.A (n + 1))) ∧
        (∀ n,
          w.condProb n false =
            (w.B (n + 1) / w.A (n + 1)) /
              (w.p (n + 1) + w.B (n + 1) / w.A (n + 1)))) := by
  refine ⟨addressValue_prefix_mod L pre tail, ?_, ?_⟩
  · intro x y hlen hx hy hxy
    exact addressValue_injective_of_digits_lt_base hL hBM hlen hx hy hxy
  · exact paper_conclusion_zg_density_exact_inhomogeneous_markov w

end Omega.Conclusion
