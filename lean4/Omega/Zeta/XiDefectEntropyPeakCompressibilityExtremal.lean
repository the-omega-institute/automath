import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- The integer part in the defect-entropy decomposition `S = M + r`. -/
noncomputable def xiDefectFloor (S : ℝ) : ℕ :=
  ⌊S⌋₊

/-- The fractional part in the defect-entropy decomposition `S = M + r`. -/
noncomputable def xiDefectFraction (S : ℝ) : ℝ :=
  S - xiDefectFloor S

/-- The extremal endpoint parameter from the interval-feasibility argument. -/
noncomputable def xiDefectAStar (κ : ℕ) (S : ℝ) : ℝ :=
  let M := xiDefectFloor S
  let r := xiDefectFraction S
  min (r / (κ - M : ℝ)) ((1 - r) / (M + 1 : ℝ))

/-- The concrete peak-compressibility profile. -/
noncomputable def xiPeakCompressibility (κ : ℕ) (S : ℝ) : ℝ :=
  4 * xiDefectAStar κ S * (1 - xiDefectAStar κ S)

/-- Existence of a separated two-value endpoint configuration with total mass `S`. -/
def xiBinaryExtremizerExists (κ : ℕ) (S : ℝ) : Prop :=
  ∃ g : List ℝ,
    g.length = κ ∧
    g.sum = S ∧
    ∀ x ∈ g, x = 0 ∨ x = xiDefectAStar κ S ∨ x = 1 - xiDefectAStar κ S ∨ x = 1

private theorem xiDefectFraction_eq (S : ℝ) :
    S = xiDefectFloor S + xiDefectFraction S := by
  simp [xiDefectFraction]

private theorem xiDefectFloor_lt {κ : ℕ} {S : ℝ} (hS0 : 0 < S) (hSκ : S < κ) :
    xiDefectFloor S < κ := by
  exact (Nat.floor_lt hS0.le).2 hSκ

private theorem xiDefectFraction_lt_one (S : ℝ) :
    xiDefectFraction S < 1 := by
  have h := Nat.lt_floor_add_one S
  dsimp [xiDefectFraction, xiDefectFloor]
  linarith

private theorem xiBinaryExtremizerExists_of_left_branch {κ : ℕ} {S : ℝ}
    (hS0 : 0 < S) (hSκ : S < κ)
    (hbranch :
      xiDefectFraction S / (κ - xiDefectFloor S : ℝ) ≤
        (1 - xiDefectFraction S) / (xiDefectFloor S + 1 : ℝ)) :
    xiBinaryExtremizerExists κ S := by
  let M := xiDefectFloor S
  let r := xiDefectFraction S
  let a := xiDefectAStar κ S
  have hMltκ : M < κ := xiDefectFloor_lt hS0 hSκ
  have hsub_pos_nat : 0 < κ - M := Nat.sub_pos_of_lt hMltκ
  have hMltκ_real : (M : ℝ) < κ := by
    exact_mod_cast hMltκ
  have hsub_ne : ((κ : ℝ) - M) ≠ 0 := by
    linarith
  have ha : a = r / (κ - M : ℝ) := by
    simp [xiDefectAStar, a, M, r, hbranch]
  refine ⟨List.replicate M 1 ++ List.replicate (κ - M) a, ?_, ?_, ?_⟩
  · simp [M, Nat.add_sub_of_le hMltκ.le]
  · rw [List.sum_append, List.sum_replicate, List.sum_replicate, ha]
    simp only [nsmul_eq_mul]
    rw [Nat.cast_sub hMltκ.le]
    calc
      (M : ℝ) * 1 + ((κ : ℝ) - M) * (r / ((κ : ℝ) - M)) = M + r := by
        field_simp [hsub_ne]
      _ = S := by
        simpa [M, r] using (xiDefectFraction_eq S).symm
  · intro x hx
    simp only [List.mem_append] at hx
    rcases hx with hx | hx
    · rcases List.mem_replicate.1 hx with ⟨_, rfl⟩
      exact Or.inr <| Or.inr <| Or.inr rfl
    · rcases List.mem_replicate.1 hx with ⟨_, rfl⟩
      exact Or.inr <| Or.inl rfl

private theorem xiBinaryExtremizerExists_of_right_branch {κ : ℕ} {S : ℝ}
    (hS0 : 0 < S) (hSκ : S < κ)
    (hbranch :
      (1 - xiDefectFraction S) / (xiDefectFloor S + 1 : ℝ) ≤
        xiDefectFraction S / (κ - xiDefectFloor S : ℝ)) :
    xiBinaryExtremizerExists κ S := by
  let M := xiDefectFloor S
  let r := xiDefectFraction S
  let a := xiDefectAStar κ S
  have hMltκ : M < κ := xiDefectFloor_lt hS0 hSκ
  have hMsucc_le : M + 1 ≤ κ := Nat.succ_le_of_lt hMltκ
  have hM1_pos : 0 < (M + 1 : ℝ) := by positivity
  have ha : a = (1 - r) / (M + 1 : ℝ) := by
    simp [xiDefectAStar, a, M, r, min_eq_right hbranch]
  refine ⟨List.replicate (M + 1) (1 - a) ++ List.replicate (κ - (M + 1)) 0, ?_, ?_, ?_⟩
  · simp [M, Nat.add_sub_of_le hMsucc_le]
  · rw [List.sum_append, List.sum_replicate, List.sum_replicate, ha]
    simp only [nsmul_eq_mul, mul_zero, add_zero]
    norm_num
    calc
      ((M : ℝ) + 1) * (1 - (1 - r) / ((M : ℝ) + 1)) = (M : ℝ) + r := by
        have hM1_ne : ((M : ℝ) + 1) ≠ 0 := by positivity
        field_simp [hM1_ne]
        ring
      _ = S := by
        simpa [M, r] using (xiDefectFraction_eq S).symm
  · intro x hx
    simp only [List.mem_append] at hx
    rcases hx with hx | hx
    · rcases List.mem_replicate.1 hx with ⟨_, rfl⟩
      exact Or.inr <| Or.inr <| Or.inl rfl
    · rcases List.mem_replicate.1 hx with ⟨_, rfl⟩
      exact Or.inl rfl

/-- The explicit peak-compressibility formula together with a concrete two-value extremizer
construction from the floor decomposition `S = M + r`.
    thm:xi-defect-entropy-peak-compressibility-extremal -/
theorem paper_xi_defect_entropy_peak_compressibility_extremal
    (κ : ℕ) (S : ℝ) (hκ : 0 < κ) (hS0 : 0 < S) (hSκ : S < κ) :
    xiPeakCompressibility κ S = 4 * xiDefectAStar κ S * (1 - xiDefectAStar κ S) ∧
      xiBinaryExtremizerExists κ S := by
  have _ := hκ
  constructor
  · rfl
  · by_cases hbranch :
        xiDefectFraction S / (κ - xiDefectFloor S : ℝ) ≤
          (1 - xiDefectFraction S) / (xiDefectFloor S + 1 : ℝ)
    · exact xiBinaryExtremizerExists_of_left_branch hS0 hSκ hbranch
    · exact xiBinaryExtremizerExists_of_right_branch hS0 hSκ (le_of_not_ge hbranch)

end Omega.Zeta
