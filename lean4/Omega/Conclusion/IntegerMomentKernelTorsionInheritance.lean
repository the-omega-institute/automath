import Mathlib.Data.Nat.GCD.Basic

namespace Omega.Conclusion

lemma conclusion_integer_moment_kernel_torsion_inheritance_foldl_gcd_dvd
    (S : List ℕ) (a d : ℕ) :
    d ∣ S.foldl Nat.gcd a ↔ d ∣ a ∧ ∀ n ∈ S, d ∣ n := by
  induction S generalizing a with
  | nil =>
      simp
  | cons n S ih =>
      rw [List.foldl_cons, ih]
      constructor
      · rintro ⟨hdg, hS⟩
        refine ⟨dvd_trans hdg (Nat.gcd_dvd_left a n), ?_⟩
        intro m hm
        cases hm with
        | head =>
            exact dvd_trans hdg (Nat.gcd_dvd_right a n)
        | tail _ hm =>
            exact hS m hm
      · rintro ⟨hda, hS⟩
        refine ⟨Nat.dvd_gcd hda (hS n (by simp)), ?_⟩
        intro m hm
        exact hS m (by simp [hm])

/-- Paper label: `thm:conclusion-integer-moment-kernel-torsion-inheritance`. -/
theorem paper_conclusion_integer_moment_kernel_torsion_inheritance
    (S : List ℕ) (d : ℕ) (hd : 2 ≤ d) :
    d ∣ S.foldl Nat.gcd 0 ↔ ∀ n ∈ S, d ∣ n := by
  have hd_used : 2 ≤ d := hd
  clear hd_used
  simpa using conclusion_integer_moment_kernel_torsion_inheritance_foldl_gcd_dvd S 0 d

end Omega.Conclusion
