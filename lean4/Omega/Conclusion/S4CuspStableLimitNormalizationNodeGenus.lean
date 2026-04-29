import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-s4-cusp-stable-limit-normalization-node-genus`. -/
theorem paper_conclusion_s4_cusp_stable_limit_normalization_node_genus
    (tail nodes b1 main : Fin 3 → ℕ)
    (htail : tail 0 = 12 ∧ tail 1 = 6 ∧ tail 2 = 4)
    (hnodes : nodes 0 = 24 ∧ nodes 1 = 12 ∧ nodes 2 = 8)
    (hb1 : ∀ i, b1 i = nodes i - tail i) (hmain : ∀ i, main i + b1 i = 16) :
    b1 0 = 12 ∧ b1 1 = 6 ∧ b1 2 = 4 ∧
      main 0 = 4 ∧ main 1 = 10 ∧ main 2 = 12 := by
  rcases htail with ⟨htail0, htail1, htail2⟩
  rcases hnodes with ⟨hnodes0, hnodes1, hnodes2⟩
  have hb10 : b1 0 = 12 := by
    calc
      b1 0 = nodes 0 - tail 0 := hb1 0
      _ = 24 - 12 := by rw [hnodes0, htail0]
      _ = 12 := by norm_num
  have hb11 : b1 1 = 6 := by
    calc
      b1 1 = nodes 1 - tail 1 := hb1 1
      _ = 12 - 6 := by rw [hnodes1, htail1]
      _ = 6 := by norm_num
  have hb12 : b1 2 = 4 := by
    calc
      b1 2 = nodes 2 - tail 2 := hb1 2
      _ = 8 - 4 := by rw [hnodes2, htail2]
      _ = 4 := by norm_num
  have hmain0 : main 0 = 4 := by
    have h := hmain 0
    rw [hb10] at h
    omega
  have hmain1 : main 1 = 10 := by
    have h := hmain 1
    rw [hb11] at h
    omega
  have hmain2 : main 2 = 12 := by
    have h := hmain 2
    rw [hb12] at h
    omega
  exact ⟨hb10, hb11, hb12, hmain0, hmain1, hmain2⟩

end Omega.Conclusion
