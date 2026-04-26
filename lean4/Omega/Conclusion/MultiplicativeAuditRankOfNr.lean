import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-multiplicative-audit-rank-of-nr`. -/
theorem paper_conclusion_multiplicative_audit_rank_of_nr (r d : ℕ) (σ : Fin d → Fin r)
    (hcoord_injective :
      Function.Injective (fun x : Fin r → ℕ => fun j : Fin d => x (σ j))) :
    r ≤ d := by
  classical
  have hsurj : Function.Surjective σ := by
    by_contra hnot
    rw [Function.Surjective] at hnot
    push_neg at hnot
    rcases hnot with ⟨i, hi⟩
    let x : Fin r → ℕ := fun _ => 0
    let y : Fin r → ℕ := fun k => if k = i then 1 else 0
    have hsame :
        (fun j : Fin d => x (σ j)) = (fun j : Fin d => y (σ j)) := by
      funext j
      simp [x, y, hi j]
    have hxy : x = y := hcoord_injective hsame
    have h01 : (0 : ℕ) = 1 := by
      have := congrArg (fun f : Fin r → ℕ => f i) hxy
      simp [x, y] at this
    exact Nat.zero_ne_one h01
  have himage : (Finset.univ.image σ : Finset (Fin r)) = Finset.univ := by
    ext i
    simp [hsurj i]
  have hcard : (Finset.univ : Finset (Fin r)).card ≤ (Finset.univ : Finset (Fin d)).card := by
    rw [← himage]
    exact Finset.card_image_le
  simpa using hcard

end Omega.Conclusion
