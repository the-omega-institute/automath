import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- A discrete linear recurrence of order `d` modeling the elimination of higher derivatives
against the first `d` jets. -/
def linearJetRecurrence (d : ℕ) (y : ℕ → ℚ) (a : ℕ → Fin d → ℚ) : Prop :=
  ∀ n : ℕ, y (n + d) = ∑ j : Fin d, a n j * y (n + j)

/-- Every jet lies in the span of the first `d` jets. -/
def dfiniteJetCompression (d : ℕ) (y : ℕ → ℚ) : Prop :=
  ∀ n : ℕ, ∃ r : Fin d → ℚ, y n = ∑ j : Fin d, r j * y j

private lemma base_jet_in_span {d n : ℕ} (hn : n < d) (y : ℕ → ℚ) :
    ∃ r : Fin d → ℚ, y n = ∑ j : Fin d, r j * y j := by
  classical
  let jn : Fin d := ⟨n, hn⟩
  refine ⟨fun j => if j = jn then 1 else 0, ?_⟩
  simp [jn]

private lemma recurrence_step_in_span
    {d : ℕ} (_hd : 0 < d) (y : ℕ → ℚ) (a : ℕ → Fin d → ℚ)
    (hrec : linearJetRecurrence d y a) :
    dfiniteJetCompression d y := by
  classical
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih
  by_cases hn : n < d
  · exact base_jet_in_span hn y
  · have hnd : d ≤ n := le_of_not_gt hn
    let m := n - d
    have hrecn : y n = ∑ j : Fin d, a m j * y (m + j) := by
      have := hrec m
      simpa [m, Nat.sub_add_cancel hnd] using this
    have hspan : ∀ j : Fin d, ∃ rj : Fin d → ℚ, y (m + j) = ∑ k : Fin d, rj k * y k := by
      intro j
      apply ih (m + j)
      have hjlt : m + (j : ℕ) < n := by
        have := Nat.add_lt_add_left j.is_lt m
        simpa [m, Nat.sub_add_cancel hnd] using this
      simpa using hjlt
    choose r hr using hspan
    refine ⟨fun k => ∑ j : Fin d, a m j * r j k, ?_⟩
    calc
      y n = ∑ j : Fin d, a m j * y (m + j) := hrecn
      _ = ∑ j : Fin d, a m j * ∑ k : Fin d, r j k * y k := by
        refine Finset.sum_congr rfl ?_
        intro j _
        rw [hr j]
      _ = ∑ k : Fin d, (∑ j : Fin d, a m j * r j k) * y k := by
        calc
          ∑ j : Fin d, a m j * ∑ k : Fin d, r j k * y k
              = ∑ j : Fin d, ∑ k : Fin d, a m j * (r j k * y k) := by
                  refine Finset.sum_congr rfl ?_
                  intro j _
                  rw [Finset.mul_sum]
          _ = ∑ k : Fin d, ∑ j : Fin d, a m j * (r j k * y k) := by
                rw [Finset.sum_comm]
          _ = ∑ k : Fin d, (∑ j : Fin d, a m j * r j k) * y k := by
                refine Finset.sum_congr rfl ?_
                intro k _
                calc
                  ∑ j : Fin d, a m j * (r j k * y k)
                      = ∑ j : Fin d, (a m j * r j k) * y k := by
                          refine Finset.sum_congr rfl ?_
                          intro j _
                          ring
                  _ = (∑ j : Fin d, a m j * r j k) * y k := by
                        rw [← Finset.sum_mul]

/-- A concrete D-finite compression theorem: an order-`d` linear recurrence for the jet sequence
forces every higher jet to be a rational linear combination of the first `d` jets.
    thm:conclusion-algebraic-ldp-dfinite-stokes-compression -/
theorem paper_conclusion_algebraic_ldp_dfinite_stokes_compression
    {d : ℕ} (hd : 0 < d) (y : ℕ → ℚ) (a : ℕ → Fin d → ℚ)
    (hrec : linearJetRecurrence d y a) :
    dfiniteJetCompression d y := by
  exact recurrence_step_in_span hd y a hrec

end Omega.Conclusion
