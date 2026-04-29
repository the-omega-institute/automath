import Omega.POM.EntropyLossFactorChainExpansion
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Omega.POM

/-- Paper label: `thm:pom-pressure-prime-edge-holographic-reconstruction`. -/
theorem paper_pom_pressure_prime_edge_holographic_reconstruction (P : ℕ → ℝ)
    (hEsc : ℕ → ℕ → ℝ) (rs : List ℕ) (hP1 : P 1 = Real.log 2)
    (hEsc_eq :
      ∀ (a r : ℕ), _root_.Omega.POM.pomEntropyLossHelper P a r =
        ((r : ℝ) - 1) * hEsc a r) :
    P rs.prod = (rs.prod : ℝ) * Real.log 2 -
      (((_root_.List.enum rs).map fun ⟨j, r⟩ =>
        ((rs.drop (j + 1)).prod : ℝ) *
          (((r : ℝ) - 1) * hEsc ((rs.take j).prod) r))).sum := by
  have hchain :
      _root_.Omega.POM.pomEntropyLossHelper P 1 rs.prod =
        (((_root_.List.enum rs).map fun ⟨j, r⟩ =>
          ((rs.drop (j + 1)).prod : ℝ) *
            _root_.Omega.POM.pomEntropyLossHelper P (1 * (rs.take j).prod) r)).sum := by
    simpa [_root_.Omega.POM.pomEntropyLossChainTerms_eq_enumMap] using
      (_root_.Omega.POM.pomEntropyLossChainTerms_sum P 1 rs)
  have hleft :
      _root_.Omega.POM.pomEntropyLossHelper P 1 rs.prod =
        (rs.prod : ℝ) * Real.log 2 - P rs.prod := by
    simp [_root_.Omega.POM.pomEntropyLossHelper, hP1]
  rw [hleft] at hchain
  simp [hEsc_eq] at hchain
  have hmap_prod_natCast (xs : List ℕ) :
      (List.map (fun n : ℕ => (n : ℝ)) xs).prod = (xs.prod : ℝ) := by
    induction xs with
    | nil => norm_num
    | cons x xs ih =>
        simp only [List.map_cons, List.prod_cons]
        rw [ih, Nat.cast_mul]
  have hdrop_prod_natCast (j : ℕ) :
      (List.drop (j + 1) (List.map (fun n : ℕ => (n : ℝ)) rs)).prod =
        ((rs.drop (j + 1)).prod : ℝ) := by
    rw [← List.map_drop (f := fun n : ℕ => (n : ℝ)) (l := rs) (i := j + 1)]
    exact hmap_prod_natCast (rs.drop (j + 1))
  have hprod_rs :
      (List.map (fun n : ℕ => (n : ℝ)) rs).prod = (rs.prod : ℝ) :=
    hmap_prod_natCast rs
  simp only [hprod_rs, hdrop_prod_natCast] at hchain
  linarith

end Omega.POM
