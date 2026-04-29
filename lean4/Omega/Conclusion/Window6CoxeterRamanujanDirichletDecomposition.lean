import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- The six-residue function space for the window-`6` profiles. -/
abbrev conclusion_window6_coxeter_ramanujan_dirichlet_decomposition_profile :=
  Fin 6 → ℚ

/-- The constant character on the six-residue window. -/
def conclusion_window6_coxeter_ramanujan_dirichlet_decomposition_one :
    conclusion_window6_coxeter_ramanujan_dirichlet_decomposition_profile :=
  fun _ => 1

/-- The long-root bare fold profile `(4,2,3,4,2,3)`. -/
def conclusion_window6_coxeter_ramanujan_dirichlet_decomposition_long_profile :
    conclusion_window6_coxeter_ramanujan_dirichlet_decomposition_profile
  | 0 => 4
  | 1 => 2
  | 2 => 3
  | 3 => 4
  | 4 => 2
  | 5 => 3

/-- The short-root bare fold profile `(4,4,4,2,4,4)`. -/
def conclusion_window6_coxeter_ramanujan_dirichlet_decomposition_short_profile :
    conclusion_window6_coxeter_ramanujan_dirichlet_decomposition_profile
  | 0 => 4
  | 1 => 4
  | 2 => 4
  | 3 => 2
  | 4 => 4
  | 5 => 4

/-- The Ramanujan vector `c₂`. -/
def conclusion_window6_coxeter_ramanujan_dirichlet_decomposition_c2 :
    conclusion_window6_coxeter_ramanujan_dirichlet_decomposition_profile
  | 0 => 1
  | 1 => -1
  | 2 => 1
  | 3 => -1
  | 4 => 1
  | 5 => -1

/-- The Ramanujan vector `c₃`. -/
def conclusion_window6_coxeter_ramanujan_dirichlet_decomposition_c3 :
    conclusion_window6_coxeter_ramanujan_dirichlet_decomposition_profile
  | 0 => 2
  | 1 => -1
  | 2 => -1
  | 3 => 2
  | 4 => -1
  | 5 => -1

/-- The Ramanujan vector `c₆`. -/
def conclusion_window6_coxeter_ramanujan_dirichlet_decomposition_c6 :
    conclusion_window6_coxeter_ramanujan_dirichlet_decomposition_profile
  | 0 => 2
  | 1 => 1
  | 2 => -1
  | 3 => -2
  | 4 => -1
  | 5 => 1

/-- The primitive real Dirichlet character modulo `3`, periodically extended to six residues. -/
def conclusion_window6_coxeter_ramanujan_dirichlet_decomposition_chi3 :
    conclusion_window6_coxeter_ramanujan_dirichlet_decomposition_profile
  | 0 => 0
  | 1 => 1
  | 2 => -1
  | 3 => 0
  | 4 => 1
  | 5 => -1

def conclusion_window6_coxeter_ramanujan_dirichlet_decomposition_statement : Prop :=
  conclusion_window6_coxeter_ramanujan_dirichlet_decomposition_long_profile =
      3 • conclusion_window6_coxeter_ramanujan_dirichlet_decomposition_one +
        (1 / 2 : ℚ) • conclusion_window6_coxeter_ramanujan_dirichlet_decomposition_c3 -
          (1 / 2 : ℚ) • conclusion_window6_coxeter_ramanujan_dirichlet_decomposition_chi3 ∧
    conclusion_window6_coxeter_ramanujan_dirichlet_decomposition_short_profile =
      (11 / 3 : ℚ) • conclusion_window6_coxeter_ramanujan_dirichlet_decomposition_one +
        (1 / 3 : ℚ) • conclusion_window6_coxeter_ramanujan_dirichlet_decomposition_c2 -
          (1 / 3 : ℚ) • conclusion_window6_coxeter_ramanujan_dirichlet_decomposition_c3 +
            (1 / 3 : ℚ) • conclusion_window6_coxeter_ramanujan_dirichlet_decomposition_c6 ∧
    conclusion_window6_coxeter_ramanujan_dirichlet_decomposition_long_profile ∈
      Submodule.span ℚ
        ({conclusion_window6_coxeter_ramanujan_dirichlet_decomposition_one,
          conclusion_window6_coxeter_ramanujan_dirichlet_decomposition_c3,
          conclusion_window6_coxeter_ramanujan_dirichlet_decomposition_chi3} : Set
            conclusion_window6_coxeter_ramanujan_dirichlet_decomposition_profile) ∧
    conclusion_window6_coxeter_ramanujan_dirichlet_decomposition_short_profile ∈
      Submodule.span ℚ
        ({conclusion_window6_coxeter_ramanujan_dirichlet_decomposition_one,
          conclusion_window6_coxeter_ramanujan_dirichlet_decomposition_c2,
          conclusion_window6_coxeter_ramanujan_dirichlet_decomposition_c3,
          conclusion_window6_coxeter_ramanujan_dirichlet_decomposition_c6} : Set
            conclusion_window6_coxeter_ramanujan_dirichlet_decomposition_profile)

lemma conclusion_window6_coxeter_ramanujan_dirichlet_decomposition_long_eq :
    conclusion_window6_coxeter_ramanujan_dirichlet_decomposition_long_profile =
      3 • conclusion_window6_coxeter_ramanujan_dirichlet_decomposition_one +
        (1 / 2 : ℚ) • conclusion_window6_coxeter_ramanujan_dirichlet_decomposition_c3 -
          (1 / 2 : ℚ) • conclusion_window6_coxeter_ramanujan_dirichlet_decomposition_chi3 := by
  ext j
  fin_cases j <;> norm_num
    [conclusion_window6_coxeter_ramanujan_dirichlet_decomposition_long_profile,
      conclusion_window6_coxeter_ramanujan_dirichlet_decomposition_one,
      conclusion_window6_coxeter_ramanujan_dirichlet_decomposition_c3,
      conclusion_window6_coxeter_ramanujan_dirichlet_decomposition_chi3]

lemma conclusion_window6_coxeter_ramanujan_dirichlet_decomposition_short_eq :
    conclusion_window6_coxeter_ramanujan_dirichlet_decomposition_short_profile =
      (11 / 3 : ℚ) • conclusion_window6_coxeter_ramanujan_dirichlet_decomposition_one +
        (1 / 3 : ℚ) • conclusion_window6_coxeter_ramanujan_dirichlet_decomposition_c2 -
          (1 / 3 : ℚ) • conclusion_window6_coxeter_ramanujan_dirichlet_decomposition_c3 +
            (1 / 3 : ℚ) • conclusion_window6_coxeter_ramanujan_dirichlet_decomposition_c6 := by
  ext j
  fin_cases j <;> norm_num
    [conclusion_window6_coxeter_ramanujan_dirichlet_decomposition_short_profile,
      conclusion_window6_coxeter_ramanujan_dirichlet_decomposition_one,
      conclusion_window6_coxeter_ramanujan_dirichlet_decomposition_c2,
      conclusion_window6_coxeter_ramanujan_dirichlet_decomposition_c3,
      conclusion_window6_coxeter_ramanujan_dirichlet_decomposition_c6]

lemma conclusion_window6_coxeter_ramanujan_dirichlet_decomposition_long_mem_span :
    conclusion_window6_coxeter_ramanujan_dirichlet_decomposition_long_profile ∈
      Submodule.span ℚ
        ({conclusion_window6_coxeter_ramanujan_dirichlet_decomposition_one,
          conclusion_window6_coxeter_ramanujan_dirichlet_decomposition_c3,
          conclusion_window6_coxeter_ramanujan_dirichlet_decomposition_chi3} : Set
            conclusion_window6_coxeter_ramanujan_dirichlet_decomposition_profile) := by
  let S : Set conclusion_window6_coxeter_ramanujan_dirichlet_decomposition_profile :=
    {conclusion_window6_coxeter_ramanujan_dirichlet_decomposition_one,
      conclusion_window6_coxeter_ramanujan_dirichlet_decomposition_c3,
      conclusion_window6_coxeter_ramanujan_dirichlet_decomposition_chi3}
  change conclusion_window6_coxeter_ramanujan_dirichlet_decomposition_long_profile ∈
    Submodule.span ℚ S
  have hone :
      conclusion_window6_coxeter_ramanujan_dirichlet_decomposition_one ∈
        Submodule.span ℚ S :=
    Submodule.subset_span (by simp [S])
  have hc3 :
      conclusion_window6_coxeter_ramanujan_dirichlet_decomposition_c3 ∈
        Submodule.span ℚ S :=
    Submodule.subset_span (by simp [S])
  have hchi :
      conclusion_window6_coxeter_ramanujan_dirichlet_decomposition_chi3 ∈
        Submodule.span ℚ S :=
    Submodule.subset_span (by simp [S])
  rw [conclusion_window6_coxeter_ramanujan_dirichlet_decomposition_long_eq]
  have hmem := Submodule.add_mem _ (Submodule.add_mem _ (Submodule.smul_mem _ (3 : ℚ) hone)
    (Submodule.smul_mem _ (1 / 2 : ℚ) hc3))
    (Submodule.neg_mem _ (Submodule.smul_mem _ (1 / 2 : ℚ) hchi))
  simpa [sub_eq_add_neg] using hmem

lemma conclusion_window6_coxeter_ramanujan_dirichlet_decomposition_short_mem_span :
    conclusion_window6_coxeter_ramanujan_dirichlet_decomposition_short_profile ∈
      Submodule.span ℚ
        ({conclusion_window6_coxeter_ramanujan_dirichlet_decomposition_one,
          conclusion_window6_coxeter_ramanujan_dirichlet_decomposition_c2,
          conclusion_window6_coxeter_ramanujan_dirichlet_decomposition_c3,
          conclusion_window6_coxeter_ramanujan_dirichlet_decomposition_c6} : Set
            conclusion_window6_coxeter_ramanujan_dirichlet_decomposition_profile) := by
  let S : Set conclusion_window6_coxeter_ramanujan_dirichlet_decomposition_profile :=
    {conclusion_window6_coxeter_ramanujan_dirichlet_decomposition_one,
      conclusion_window6_coxeter_ramanujan_dirichlet_decomposition_c2,
      conclusion_window6_coxeter_ramanujan_dirichlet_decomposition_c3,
      conclusion_window6_coxeter_ramanujan_dirichlet_decomposition_c6}
  change conclusion_window6_coxeter_ramanujan_dirichlet_decomposition_short_profile ∈
    Submodule.span ℚ S
  have hone :
      conclusion_window6_coxeter_ramanujan_dirichlet_decomposition_one ∈
        Submodule.span ℚ S :=
    Submodule.subset_span (by simp [S])
  have hc2 :
      conclusion_window6_coxeter_ramanujan_dirichlet_decomposition_c2 ∈
        Submodule.span ℚ S :=
    Submodule.subset_span (by simp [S])
  have hc3 :
      conclusion_window6_coxeter_ramanujan_dirichlet_decomposition_c3 ∈
        Submodule.span ℚ S :=
    Submodule.subset_span (by simp [S])
  have hc6 :
      conclusion_window6_coxeter_ramanujan_dirichlet_decomposition_c6 ∈
        Submodule.span ℚ S :=
    Submodule.subset_span (by simp [S])
  rw [conclusion_window6_coxeter_ramanujan_dirichlet_decomposition_short_eq]
  have hmem := Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
    (Submodule.smul_mem _ (11 / 3 : ℚ) hone)
    (Submodule.smul_mem _ (1 / 3 : ℚ) hc2))
    (Submodule.neg_mem _ (Submodule.smul_mem _ (1 / 3 : ℚ)
      hc3)))
    (Submodule.smul_mem _ (1 / 3 : ℚ) hc6)
  simpa [sub_eq_add_neg, add_assoc] using hmem

/-- Paper label: `thm:conclusion-window6-coxeter-ramanujan-dirichlet-decomposition`. -/
theorem paper_conclusion_window6_coxeter_ramanujan_dirichlet_decomposition :
    conclusion_window6_coxeter_ramanujan_dirichlet_decomposition_statement := by
  exact ⟨conclusion_window6_coxeter_ramanujan_dirichlet_decomposition_long_eq,
    conclusion_window6_coxeter_ramanujan_dirichlet_decomposition_short_eq,
    conclusion_window6_coxeter_ramanujan_dirichlet_decomposition_long_mem_span,
    conclusion_window6_coxeter_ramanujan_dirichlet_decomposition_short_mem_span⟩

end Omega.Conclusion
