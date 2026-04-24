import Omega.Folding.MaxFiberTwoStep

namespace Omega

/-- Paper label: `thm:fold-top-two-zeckendorf-trisect`.
The three-count statement packages the existing hidden-bit counts and their even/odd closed forms. -/
theorem paper_fold_top_two_zeckendorf_trisect (m : Nat) (hm : 2 <= m) :
    ((Finset.univ.filter (fun w : Omega.Word m => Omega.hiddenBit w = 1)).card =
      Omega.hiddenBitCount m) ∧
    ((Finset.univ.filter (fun w : Omega.Word m => Omega.hiddenBit w = 0)).card =
      2 ^ m - Omega.hiddenBitCount m) ∧
    (if m % 2 = 0 then 3 * Omega.hiddenBitCount m = 4 ^ (m / 2) - 1
     else 3 * Omega.hiddenBitCount m = 2 * 4 ^ (m / 2) - 2) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold Omega.hiddenBitCount
    congr 1
    ext w
    simp [Omega.hiddenBit]
  · simpa [Omega.hiddenBit] using Omega.complement_hiddenBitCount m
  · by_cases heven : m % 2 = 0
    · simp [heven]
      have hmEven : 2 ∣ m := Nat.dvd_of_mod_eq_zero heven
      obtain ⟨k, rfl⟩ := hmEven
      have hk : 1 ≤ k := by omega
      simpa using Omega.hiddenBitCount_even_closed k hk
    · have hodd : m % 2 = 1 := by omega
      simp [hodd]
      obtain ⟨k, hk⟩ : ∃ k, m = 2 * k + 1 := ⟨m / 2, by omega⟩
      rw [hk]
      have hdiv : (2 * k + 1) / 2 = k := by omega
      simpa [hdiv] using Omega.hiddenBitCount_odd_closed k

end Omega
