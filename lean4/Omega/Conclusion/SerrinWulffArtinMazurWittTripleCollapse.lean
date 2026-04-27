import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-serrin-wulff-artin-mazur-witt-triple-collapse`. -/
theorem paper_conclusion_serrin_wulff_artin_mazur_witt_triple_collapse
    {Y : ℕ → Type*} (rho : ∀ m, Y (m + 1) → Y m)
    (hYsub : ∀ m, Subsingleton (Y m)) (hYnonempty : ∀ m, Nonempty (Y m))
    (p : ℕ → ℕ) (hp : p = fun n => if n = 1 then 1 else 0) :
    (∀ m, Subsingleton (Y m)) ∧
      Nonempty { y : (m : ℕ) → Y m // ∀ m, rho m (y (m + 1)) = y m } ∧
      Subsingleton { y : (m : ℕ) → Y m // ∀ m, rho m (y (m + 1)) = y m } ∧
      p 1 = 1 ∧ (∀ n, 2 ≤ n → p n = 0) := by
  refine ⟨hYsub, ?_, ?_, ?_, ?_⟩
  · refine ⟨⟨fun m => Classical.choice (hYnonempty m), ?_⟩⟩
    intro m
    exact Subsingleton.elim _ _
  · constructor
    intro y z
    ext m
    exact Subsingleton.elim _ _
  · simp [hp]
  · intro n hn
    have hn_ne_one : n ≠ 1 := by omega
    simp [hp, hn_ne_one]

end Omega.Conclusion
