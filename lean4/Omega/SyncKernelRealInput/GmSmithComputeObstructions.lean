import Mathlib.Tactic

namespace Omega.SyncKernelRealInput

/-- Paper label: `prop:gm-smith-compute-obstructions`. -/
theorem paper_gm_smith_compute_obstructions
    (cycleWeights : List ℤ) :
    ∃ d : ℕ, d = cycleWeights.foldl (fun acc z => Nat.gcd acc z.natAbs) 0 ∧
      ∀ z ∈ cycleWeights, d ∣ z.natAbs := by
  refine ⟨cycleWeights.foldl (fun acc z => Nat.gcd acc z.natAbs) 0, rfl, ?_⟩
  have hfold :
      ∀ (xs : List ℤ) (acc : ℕ),
        xs.foldl (fun acc z => Nat.gcd acc z.natAbs) acc ∣ acc ∧
          ∀ z ∈ xs, xs.foldl (fun acc z => Nat.gcd acc z.natAbs) acc ∣ z.natAbs := by
    intro xs
    induction xs with
    | nil =>
        intro acc
        simp
    | cons x xs ih =>
        intro acc
        have h := ih (Nat.gcd acc (Int.natAbs x))
        have hdiv_x :
            xs.foldl (fun acc z => Nat.gcd acc z.natAbs) (Nat.gcd acc (Int.natAbs x)) ∣
              Int.natAbs x :=
          dvd_trans h.1 (Nat.gcd_dvd_right acc (Int.natAbs x))
        constructor
        · exact dvd_trans h.1 (Nat.gcd_dvd_left acc (Int.natAbs x))
        · intro z hz
          simp only [List.mem_cons] at hz
          rcases hz with rfl | hz
          · exact hdiv_x
          · exact h.2 z hz
  exact (hfold cycleWeights 0).2

end Omega.SyncKernelRealInput
