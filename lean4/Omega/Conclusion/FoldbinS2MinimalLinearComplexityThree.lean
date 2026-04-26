import Mathlib.Tactic
import Omega.Folding.MomentRecurrence

namespace Omega.Conclusion

/-- Paper-facing `S_2` sequence on integer coefficients. -/
noncomputable def conclusion_foldbin_s2_minimal_linear_complexity_three_foldbinS2 (n : ℕ) : Int :=
  momentSum 2 n

local notation "foldbinS2" => conclusion_foldbin_s2_minimal_linear_complexity_three_foldbinS2

/-- Paper label: `thm:conclusion-foldbin-s2-minimal-linear-complexity-three`. The existing
order-`3` recurrence for `momentSum 2` gives the claimed recurrence for `foldbinS2`, and the first
two recurrence equations already rule out every order-`2` integer-coefficient relation. -/
theorem paper_conclusion_foldbin_s2_minimal_linear_complexity_three :
    (∀ n ≥ 3, foldbinS2 (n + 1) = 2 * foldbinS2 n + 2 * foldbinS2 (n - 1) - 2 * foldbinS2 (n - 2)) ∧
      ¬ ∃ a b : Int, ∀ n ≥ 2, foldbinS2 (n + 1) = a * foldbinS2 n + b * foldbinS2 (n - 1) := by
  refine ⟨?_, ?_⟩
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
    have hNat : momentSum 2 ((k + 1) + 3) + 2 * momentSum 2 (k + 1) =
        2 * momentSum 2 ((k + 1) + 2) + 2 * momentSum 2 ((k + 1) + 1) :=
      momentSum_two_recurrence (k + 1)
    have hIntBase : ((momentSum 2 (k + 4) : Int) + 2 * (momentSum 2 (k + 1) : Int) =
        2 * (momentSum 2 (k + 3) : Int) + 2 * (momentSum 2 (k + 2) : Int)) := by
      exact_mod_cast hNat
    have hInt : foldbinS2 (k + 4) + 2 * foldbinS2 (k + 1) =
        2 * foldbinS2 (k + 3) + 2 * foldbinS2 (k + 2) := by
      simpa [conclusion_foldbin_s2_minimal_linear_complexity_three_foldbinS2] using hIntBase
    have hRec : foldbinS2 (k + 4) =
        2 * foldbinS2 (k + 3) + 2 * foldbinS2 (k + 2) - 2 * foldbinS2 (k + 1) := by
      linarith
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hRec
  · rintro ⟨a, b, hrec⟩
    have h2 := hrec 2 (by omega)
    have h3 := hrec 3 (by omega)
    have h2' : (14 : Int) = a * 6 + b * 2 := by
      simpa [conclusion_foldbin_s2_minimal_linear_complexity_three_foldbinS2, momentSum_two_one,
        momentSum_two_two, momentSum_two_three] using h2
    have h3' : (36 : Int) = a * 14 + b * 6 := by
      simpa [conclusion_foldbin_s2_minimal_linear_complexity_three_foldbinS2, momentSum_two_two,
        momentSum_two_three, momentSum_two_four] using h3
    omega

end Omega.Conclusion
