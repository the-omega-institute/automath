import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

lemma gm_resonant_character_group_homology_foldl_gcd_dvd
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

lemma gm_resonant_character_group_homology_foldl_gcd_greatest
    (cycleWeights : List ℤ) (acc : ℕ) :
    ∀ e : ℕ,
      e ∣ acc →
        (∀ z ∈ cycleWeights, e ∣ z.natAbs) →
          e ∣ cycleWeights.foldl (fun acc z => Nat.gcd acc z.natAbs) acc := by
  induction cycleWeights generalizing acc with
  | nil =>
      intro e heacc _
      simpa using heacc
  | cons z zs ih =>
      intro e heacc hall
      dsimp [List.foldl]
      refine ih (Nat.gcd acc z.natAbs) e ?_ ?_
      · exact Nat.dvd_gcd heacc (hall z (by simp))
      · intro y hy
        exact hall y (by simp [hy])

/-- Paper label: `thm:gm-resonant-character-group-homology`. -/
theorem paper_gm_resonant_character_group_homology (cycleWeights : List ℤ) :
    ∃ d : ℕ,
      d = cycleWeights.foldl (fun acc z => Nat.gcd acc z.natAbs) 0 ∧
        (∀ z ∈ cycleWeights, d ∣ z.natAbs) ∧
          (∀ e : ℕ, (∀ z ∈ cycleWeights, e ∣ z.natAbs) → e ∣ d) := by
  refine ⟨cycleWeights.foldl (fun acc z => Nat.gcd acc z.natAbs) 0, rfl, ?_, ?_⟩
  · exact (gm_resonant_character_group_homology_foldl_gcd_dvd cycleWeights 0).2
  · intro e he
    exact gm_resonant_character_group_homology_foldl_gcd_greatest cycleWeights 0 e
      (Nat.dvd_zero e) he

end Omega.SyncKernelWeighted
