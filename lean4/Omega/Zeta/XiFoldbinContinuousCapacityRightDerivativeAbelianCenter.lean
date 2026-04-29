import Mathlib.Tactic

namespace Omega.Zeta

/-- Finite fiber-count data for the fold-bin continuous capacity derivative ledger.  The
`fiberDegree` value is read as the number of sheets over a labeled finite fiber. -/
structure xi_foldbin_continuous_capacity_right_derivative_abelian_center_data where
  support : Finset ℕ
  fiberDegree : ℕ → ℕ

namespace xi_foldbin_continuous_capacity_right_derivative_abelian_center_data

/-- The `k`-th right slope is the number of finite fibers whose degree is at least `k + 1`. -/
def rightSlope
    (D : xi_foldbin_continuous_capacity_right_derivative_abelian_center_data) (k : ℕ) : ℕ :=
  (D.support.filter fun a => k + 1 ≤ D.fiberDegree a).card

/-- Abelian rank counts the fibers of degree at least two. -/
def abelianRank (D : xi_foldbin_continuous_capacity_right_derivative_abelian_center_data) :
    ℕ :=
  (D.support.filter fun a => 2 ≤ D.fiberDegree a).card

/-- The center is the degree-two stratum. -/
def centerRank (D : xi_foldbin_continuous_capacity_right_derivative_abelian_center_data) :
    ℕ :=
  (D.support.filter fun a => D.fiberDegree a = 2).card

/-- Noncentral abelian directions are precisely the fibers of degree at least three. -/
def noncentralAbelianRank
    (D : xi_foldbin_continuous_capacity_right_derivative_abelian_center_data) : ℕ :=
  (D.support.filter fun a => 3 ≤ D.fiberDegree a).card

end xi_foldbin_continuous_capacity_right_derivative_abelian_center_data

/-- Paper label: `thm:xi-foldbin-continuous-capacity-right-derivative-abelian-center`. -/
theorem paper_xi_foldbin_continuous_capacity_right_derivative_abelian_center
    (D : xi_foldbin_continuous_capacity_right_derivative_abelian_center_data) :
    D.rightSlope 1 = D.abelianRank ∧
      D.centerRank = D.rightSlope 1 - D.rightSlope 2 ∧
        D.noncentralAbelianRank = D.rightSlope 2 := by
  classical
  have hsubset :
      D.support.filter (fun a => 3 ≤ D.fiberDegree a) ⊆
        D.support.filter (fun a => 2 ≤ D.fiberDegree a) := by
    intro a ha
    simp only [Finset.mem_filter] at ha ⊢
    exact ⟨ha.1, by omega⟩
  have hsdiff :
      D.support.filter (fun a => 2 ≤ D.fiberDegree a) \
          D.support.filter (fun a => 3 ≤ D.fiberDegree a) =
        D.support.filter (fun a => D.fiberDegree a = 2) := by
    ext a
    simp only [Finset.mem_sdiff, Finset.mem_filter]
    constructor
    · rintro ⟨⟨ha, htwo⟩, hnotThree⟩
      have hnot : ¬3 ≤ D.fiberDegree a := by
        intro hthree
        exact hnotThree ⟨ha, hthree⟩
      exact ⟨ha, by omega⟩
    · rintro ⟨ha, hdeg⟩
      exact ⟨⟨ha, by omega⟩, by omega⟩
  have hcenter :
      (D.support.filter (fun a => D.fiberDegree a = 2)).card =
        (D.support.filter (fun a => 2 ≤ D.fiberDegree a)).card -
          (D.support.filter (fun a => 3 ≤ D.fiberDegree a)).card := by
    rw [← hsdiff, Finset.card_sdiff]
    rw [Finset.inter_eq_left.mpr hsubset]
  refine ⟨?_, ?_, ?_⟩
  · simp [xi_foldbin_continuous_capacity_right_derivative_abelian_center_data.rightSlope,
      xi_foldbin_continuous_capacity_right_derivative_abelian_center_data.abelianRank]
  · simpa [xi_foldbin_continuous_capacity_right_derivative_abelian_center_data.rightSlope,
      xi_foldbin_continuous_capacity_right_derivative_abelian_center_data.centerRank] using
      hcenter
  · simp [xi_foldbin_continuous_capacity_right_derivative_abelian_center_data.rightSlope,
      xi_foldbin_continuous_capacity_right_derivative_abelian_center_data.noncentralAbelianRank]

end Omega.Zeta
