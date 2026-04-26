import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- Concrete finite-set package for the singular-support projection audit of the tripling curve. -/
structure xi_terminal_zm_elliptic_weight_tripling_singularity_projection_data where
  singularSupport : Finset ℕ
  indexZeroSet : Finset ℕ
  leeYangBranchSet : Finset ℕ
  a32Zeros : Finset ℕ
  b66Zeros : Finset ℕ
  delta : ℕ → ℕ
  singularSupportInsideIndexZero : singularSupport ⊆ indexZeroSet
  indexZeroCoveredBySupport : indexZeroSet.card ≤ singularSupport.card
  indexZeroSet_eq_union : indexZeroSet = a32Zeros ∪ b66Zeros
  a32Zeros_card_eq : a32Zeros.card = 32
  b66Zeros_card_eq : b66Zeros.card = 66
  a32_b66_disjoint : Disjoint a32Zeros b66Zeros
  indexZero_leeYang_disjoint : Disjoint indexZeroSet leeYangBranchSet
  totalDelta_eq : Finset.sum singularSupport delta = 104
  delta_ge_one : ∀ P ∈ singularSupport, 1 ≤ delta P

namespace xi_terminal_zm_elliptic_weight_tripling_singularity_projection_data

/-- The quantitative support bounds asserted for the geometric singular set. -/
def support_bounds
    (D : xi_terminal_zm_elliptic_weight_tripling_singularity_projection_data) : Prop :=
  98 ≤ D.singularSupport.card ∧ D.singularSupport.card ≤ 104

/-- At most six singularities have `δ_P ≥ 2`. -/
def delta_excess_bound
    (D : xi_terminal_zm_elliptic_weight_tripling_singularity_projection_data) : Prop :=
  (D.singularSupport.filter (fun P => 2 ≤ D.delta P)).card ≤ 6

lemma indexZeroSet_card_eq_98
    (D : xi_terminal_zm_elliptic_weight_tripling_singularity_projection_data) :
    D.indexZeroSet.card = 98 := by
  calc
    D.indexZeroSet.card = (D.a32Zeros ∪ D.b66Zeros).card := by
      rw [D.indexZeroSet_eq_union]
    _ = D.a32Zeros.card + D.b66Zeros.card := by
      exact Finset.card_union_of_disjoint D.a32_b66_disjoint
    _ = 98 := by
      rw [D.a32Zeros_card_eq, D.b66Zeros_card_eq]

lemma singularSupport_card_le_totalDelta
    (D : xi_terminal_zm_elliptic_weight_tripling_singularity_projection_data) :
    D.singularSupport.card ≤ 104 := by
  calc
    D.singularSupport.card = Finset.sum D.singularSupport (fun _P => 1) := by
      simp
    _ ≤ Finset.sum D.singularSupport D.delta := by
      exact Finset.sum_le_sum (by
        intro P hP
        exact D.delta_ge_one P hP)
    _ = 104 := D.totalDelta_eq

lemma support_bounds_of_projection
    (D : xi_terminal_zm_elliptic_weight_tripling_singularity_projection_data) :
    D.support_bounds := by
  constructor
  · calc
      98 = D.indexZeroSet.card := (D.indexZeroSet_card_eq_98).symm
      _ ≤ D.singularSupport.card := D.indexZeroCoveredBySupport
  · exact D.singularSupport_card_le_totalDelta

lemma high_delta_card_add_support_card_le_totalDelta
    (D : xi_terminal_zm_elliptic_weight_tripling_singularity_projection_data) :
    D.singularSupport.card +
        (D.singularSupport.filter (fun P => 2 ≤ D.delta P)).card ≤ 104 := by
  let high := D.singularSupport.filter (fun P => 2 ≤ D.delta P)
  let low := D.singularSupport.filter (fun P => ¬ 2 ≤ D.delta P)
  have hpartition : D.singularSupport = high ∪ low := by
    ext P
    simp [high, low]
    constructor
    · intro hP
      by_cases hdelta : 2 ≤ D.delta P
      · exact Or.inl ⟨hP, hdelta⟩
      · exact Or.inr ⟨hP, Nat.lt_of_not_ge hdelta⟩
    · intro hP
      exact hP.elim (fun h => h.1) (fun h => h.1)
  have hdisjoint : Disjoint high low := by
    rw [Finset.disjoint_left]
    intro P hPhigh hPlow
    simp [high] at hPhigh
    simp [low] at hPlow
    exact (not_lt_of_ge hPhigh.2) hPlow.2
  have hcard :
      D.singularSupport.card + high.card = 2 * high.card + low.card := by
    calc
      D.singularSupport.card + high.card = (high ∪ low).card + high.card := by
        rw [hpartition]
      _ = (high.card + low.card) + high.card := by
        rw [Finset.card_union_of_disjoint hdisjoint]
      _ = 2 * high.card + low.card := by
        omega
  have hsumHigh : 2 * high.card ≤ Finset.sum high D.delta := by
    calc
      2 * high.card = Finset.sum high (fun _P => 2) := by
        rw [Finset.sum_const]
        simp [Nat.mul_comm]
      _ ≤ Finset.sum high D.delta := by
        exact Finset.sum_le_sum (by
          intro P hP
          simp [high] at hP
          exact hP.2)
  have hsumLow : low.card ≤ Finset.sum low D.delta := by
    calc
      low.card = Finset.sum low (fun _P => 1) := by
        rw [Finset.sum_const]
        simp
      _ ≤ Finset.sum low D.delta := by
        exact Finset.sum_le_sum (by
          intro P hP
          simp [low] at hP
          exact D.delta_ge_one P hP.1)
  have hsumParts :
      Finset.sum D.singularSupport D.delta =
        Finset.sum high D.delta + Finset.sum low D.delta := by
    rw [hpartition, Finset.sum_union hdisjoint]
  calc
    D.singularSupport.card + high.card = 2 * high.card + low.card := hcard
    _ ≤ Finset.sum high D.delta + Finset.sum low D.delta :=
      Nat.add_le_add hsumHigh hsumLow
    _ = Finset.sum D.singularSupport D.delta := hsumParts.symm
    _ = 104 := D.totalDelta_eq

lemma delta_excess_bound_of_totalDelta
    (D : xi_terminal_zm_elliptic_weight_tripling_singularity_projection_data) :
    D.delta_excess_bound := by
  have hsupport : 98 ≤ D.singularSupport.card := (D.support_bounds_of_projection).1
  have hsum := D.high_delta_card_add_support_card_le_totalDelta
  dsimp [delta_excess_bound]
  omega

end xi_terminal_zm_elliptic_weight_tripling_singularity_projection_data

open xi_terminal_zm_elliptic_weight_tripling_singularity_projection_data

/-- Paper label:
`thm:xi-terminal-zm-elliptic-weight-tripling-singularity-projection`. -/
theorem paper_xi_terminal_zm_elliptic_weight_tripling_singularity_projection
    (D : xi_terminal_zm_elliptic_weight_tripling_singularity_projection_data) :
    D.support_bounds ∧ D.delta_excess_bound := by
  exact ⟨D.support_bounds_of_projection, D.delta_excess_bound_of_totalDelta⟩

end Omega.Zeta
