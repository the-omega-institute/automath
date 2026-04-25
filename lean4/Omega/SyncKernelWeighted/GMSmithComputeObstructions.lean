import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

private lemma gm_smith_compute_obstructions_foldl_gcd_dvd
    (cycleWeights : List ℤ) (acc : ℕ) :
    cycleWeights.foldl (fun acc z => Nat.gcd acc z.natAbs) acc ∣ acc ∧
      ∀ z ∈ cycleWeights,
        cycleWeights.foldl (fun acc z => Nat.gcd acc z.natAbs) acc ∣ z.natAbs := by
  induction cycleWeights generalizing acc with
  | nil =>
      simp
  | cons z zs ih =>
      dsimp [List.foldl]
      have h := ih (Nat.gcd acc z.natAbs)
      constructor
      · exact h.1.trans (Nat.gcd_dvd_left acc z.natAbs)
      · intro y hy
        simp only [List.mem_cons] at hy
        rcases hy with hy | hy
        · rw [hy]
          exact h.1.trans (Nat.gcd_dvd_right acc z.natAbs)
        · exact h.2 y hy

/-- Paper label: `prop:gm-smith-compute-obstructions`. -/
theorem paper_gm_smith_compute_obstructions (cycleWeights : List ℤ) :
    ∃ d : ℕ,
      d = cycleWeights.foldl (fun acc z => Nat.gcd acc z.natAbs) 0 ∧
        ∀ z ∈ cycleWeights, d ∣ z.natAbs := by
  refine ⟨cycleWeights.foldl (fun acc z => Nat.gcd acc z.natAbs) 0, rfl, ?_⟩
  exact (gm_smith_compute_obstructions_foldl_gcd_dvd cycleWeights 0).2

end Omega.SyncKernelWeighted
