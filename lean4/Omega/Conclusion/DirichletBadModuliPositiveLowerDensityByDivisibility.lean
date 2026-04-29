import Mathlib.Tactic

namespace Omega.Conclusion

/-- Multiples of a fixed positive modulus inject into the bad moduli up to `X`, giving the finite
counting lower bound behind the positive lower-density corollary.
    cor:conclusion-dirichlet-bad-moduli-positive-lower-density-by-divisibility -/
theorem paper_conclusion_dirichlet_bad_moduli_positive_lower_density_by_divisibility
    (bad : ℕ → Prop) [DecidablePred bad] (m0 : ℕ) (hm0 : 1 ≤ m0)
    (hmul : ∀ l : ℕ, 1 ≤ l → bad (l * m0)) :
    (∀ l : ℕ, 1 ≤ l → bad (l * m0)) ∧
      ∀ X : ℕ, X / m0 ≤ ((Finset.Icc 1 X).filter (fun n => bad n)).card := by
  refine ⟨hmul, ?_⟩
  intro X
  let source := Finset.Icc 1 (X / m0)
  let target := (Finset.Icc 1 X).filter (fun n => bad n)
  have hm0_pos : 0 < m0 := Nat.succ_le_iff.mp hm0
  have hsource_card : source.card = X / m0 := by
    simp [source, Nat.card_Icc]
  have hcount : source.card ≤ target.card := by
    apply Finset.card_le_card_of_injOn (fun l : ℕ => l * m0)
    · intro l hl
      have hlIcc : l ∈ Finset.Icc 1 (X / m0) := by simpa [source] using hl
      have hl_ge : 1 ≤ l := (Finset.mem_Icc.mp hlIcc).1
      have hl_le : l ≤ X / m0 := (Finset.mem_Icc.mp hlIcc).2
      have h_lower : 1 ≤ l * m0 := by
        calc
          1 = 1 * 1 := by norm_num
          _ ≤ l * m0 := Nat.mul_le_mul hl_ge hm0
      have h_upper : l * m0 ≤ X := (Nat.le_div_iff_mul_le hm0_pos).mp hl_le
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨h_lower, h_upper⟩, hmul l hl_ge⟩
    · intro a _ b _ h
      exact Nat.eq_of_mul_eq_mul_right hm0_pos h
  simpa [source, target, hsource_card] using hcount

end Omega.Conclusion
