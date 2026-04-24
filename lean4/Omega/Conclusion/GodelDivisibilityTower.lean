import Mathlib.Data.Nat.Basic

namespace Omega.Conclusion

/-- Paper label: `prop:conclusion-godel-divisibility-tower`. -/
theorem paper_conclusion_godel_divisibility_tower (nSeq : ℕ → ℕ)
    (hstep : ∀ n, nSeq n ∣ nSeq (n + 1)) : ∀ {n m : ℕ}, n ≤ m → nSeq n ∣ nSeq m := by
  intro n m hnm
  induction hnm with
  | refl =>
      exact ⟨1, by simp⟩
  | @step m hnm ih =>
      rcases ih with ⟨a, ha⟩
      rcases hstep m with ⟨b, hb⟩
      refine ⟨a * b, ?_⟩
      calc
        nSeq (m + 1) = nSeq m * b := hb
        _ = (nSeq n * a) * b := by rw [ha]
        _ = nSeq n * (a * b) := by rw [Nat.mul_assoc]

end Omega.Conclusion
