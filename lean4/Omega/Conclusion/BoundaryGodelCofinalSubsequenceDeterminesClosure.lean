import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-boundary-godel-cofinal-subsequence-determines-closure`. -/
theorem paper_conclusion_boundary_godel_cofinal_subsequence_determines_closure
    {Point Code : Type} (decode : Code → Point → Prop) (H : Nat → Code) (m : Nat → Nat)
    (closure : Point → Prop)
    (hclosure : ∀ x, closure x ↔ ∀ j, decode (H (m j)) x) :
    ∀ x, closure x ↔ ∀ j, decode (H (m j)) x := by
  exact hclosure

/-- Paper label: `cor:conclusion-boundary-godel-zero-density-resolution-archive-complete`. -/
theorem paper_conclusion_boundary_godel_zero_density_resolution_archive_complete
    {Point Code : Type} (decode : Code → Point → Prop) (H : ℕ → Code) (M : Set ℕ)
    (hM : ∀ N, ∃ m ∈ M, N ≤ m) (closure : Point → Prop)
    (hclosure :
      ∀ m : ℕ → ℕ,
        StrictMono m →
        (∀ j, m j ∈ M) →
        (∀ x, closure x ↔ ∀ j, decode (H (m j)) x)) :
    ∃ m : ℕ → ℕ,
      StrictMono m ∧
        (∀ j, m j ∈ M) ∧ (∀ x, closure x ↔ ∀ j, decode (H (m j)) x) := by
  classical
  let step : ℕ → ℕ := fun N => Classical.choose (hM N)
  have hstep_mem : ∀ N, step N ∈ M := fun N => (Classical.choose_spec (hM N)).1
  have hstep_ge : ∀ N, N ≤ step N := fun N => (Classical.choose_spec (hM N)).2
  let m : ℕ → ℕ := fun n => Nat.recOn n (step 0) (fun _ acc => step (acc + 1))
  have hm_succ : ∀ j, m (j + 1) = step (m j + 1) := fun _ => rfl
  have hm_mem : ∀ j, m j ∈ M := by
    intro j
    cases j with
    | zero =>
        exact hstep_mem 0
    | succ j =>
        rw [hm_succ j]
        exact hstep_mem (m j + 1)
  have hm_lt_succ : ∀ j, m j < m (j + 1) := by
    intro j
    rw [hm_succ j]
    exact Nat.lt_of_succ_le (by simpa [Nat.succ_eq_add_one] using hstep_ge (m j + 1))
  have hm_strict : StrictMono m := strictMono_nat_of_lt_succ hm_lt_succ
  exact ⟨m, hm_strict, hm_mem, hclosure m hm_strict hm_mem⟩

end Omega.Conclusion
