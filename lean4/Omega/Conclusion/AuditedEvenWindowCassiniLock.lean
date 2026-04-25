import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-audited-even-window-cassini-lock`. -/
theorem paper_conclusion_audited_even_window_cassini_lock (F : Nat → Int) (h0 : F 0 = 0)
    (h1 : F 1 = 1) (hrec : ∀ n : Nat, F (n + 2) = F (n + 1) + F n) {m : Nat}
    (hm : m = 6 ∨ m = 8 ∨ m = 10 ∨ m = 12) {M L X : Int} (hM : M = F m)
    (hL : L = F (m + 1)) (hX : X = F (m + 2)) :
    L ^ 2 - M * X = 1 := by
  have h2 : F 2 = 1 := by
    simpa [h0, h1] using hrec 0
  have h3 : F 3 = 2 := by
    simpa [h1, h2] using hrec 1
  have h4 : F 4 = 3 := by
    simpa [h2, h3] using hrec 2
  have h5 : F 5 = 5 := by
    simpa [h3, h4] using hrec 3
  have h6 : F 6 = 8 := by
    simpa [h4, h5] using hrec 4
  have h7 : F 7 = 13 := by
    simpa [h5, h6] using hrec 5
  have h8 : F 8 = 21 := by
    simpa [h6, h7] using hrec 6
  have h9 : F 9 = 34 := by
    simpa [h7, h8] using hrec 7
  have h10 : F 10 = 55 := by
    simpa [h8, h9] using hrec 8
  have h11 : F 11 = 89 := by
    simpa [h9, h10] using hrec 9
  have h12 : F 12 = 144 := by
    simpa [h10, h11] using hrec 10
  have h13 : F 13 = 233 := by
    simpa [h11, h12] using hrec 11
  have h14 : F 14 = 377 := by
    simpa [h12, h13] using hrec 12
  rcases hm with rfl | rfl | rfl | rfl
  · subst M
    subst L
    subst X
    norm_num [h6, h7, h8]
  · subst M
    subst L
    subst X
    norm_num [h8, h9, h10]
  · subst M
    subst L
    subst X
    norm_num [h10, h11, h12]
  · subst M
    subst L
    subst X
    norm_num [h12, h13, h14]

end Omega.Conclusion
