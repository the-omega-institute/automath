import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic
import Omega.POM.DiagonalRateDiagonalStatisticsComplete
import Omega.POM.DiagonalRateRefreshHittingTimeMeanClosed

namespace Omega.POM

open scoped BigOperators

/-- The refresh-rate function recovered from the diagonal statistic `p_δ`. -/
def pom_diagonal_rate_diagonal_determines_commute_refreshRate {α : Type*}
    (κ : ℚ) (p : α → ℚ) (x : α) : ℚ :=
  1 - (κ / (1 + κ)) * p x

/-- The star normalizer `S_δ = ∑_z π_δ(z) / r_δ(z)`. -/
def pom_diagonal_rate_diagonal_determines_commute_normalizer {α : Type*} [Fintype α]
    (π r : α → ℚ) : ℚ :=
  ∑ z, π z / r z

/-- The commute time obtained by summing the two directional mean hitting times. -/
noncomputable def pom_diagonal_rate_diagonal_determines_commute_commuteTime {α : Type*} [Fintype α]
    [DecidableEq α] (r π : α → ℚ) (x y : α) : ℚ :=
  diagonalRateAbsorbingMeanHitTime r π x y + diagonalRateAbsorbingMeanHitTime r π y x

private lemma pom_diagonal_rate_diagonal_determines_commute_deleted_sum
    {α : Type*} [Fintype α] [DecidableEq α] (π r : α → ℚ) (y : α) :
    (∑ z, if z = y then 0 else π z / r z) =
      pom_diagonal_rate_diagonal_determines_commute_normalizer π r - π y / r y := by
  classical
  have hy : y ∈ (Finset.univ : Finset α) := by simp
  calc
    (∑ z, if z = y then 0 else π z / r z)
        = Finset.sum (Finset.erase (Finset.univ : Finset α) y)
            (fun z => if z = y then 0 else π z / r z) := by
            rw [← Finset.sum_erase_add
              (s := (Finset.univ : Finset α))
              (a := y)
              (f := fun z => if z = y then 0 else π z / r z) hy]
            simp
    _ = Finset.sum (Finset.erase (Finset.univ : Finset α) y) (fun z => π z / r z) := by
          refine Finset.sum_congr rfl ?_
          intro z hz
          simp [(Finset.mem_erase.mp hz).1]
    _ = (∑ z : α, π z / r z) - π y / r y := by
          rw [eq_sub_iff_add_eq]
          simpa [hy, add_comm, add_left_comm, add_assoc] using
            (Finset.sum_erase_add (s := Finset.univ) (a := y) (f := fun z => π z / r z) hy).symm
    _ = pom_diagonal_rate_diagonal_determines_commute_normalizer π r - π y / r y := by
          rfl

/-- Paper label: `cor:pom-diagonal-rate-diagonal-determines-commute`. -/
theorem paper_pom_diagonal_rate_diagonal_determines_commute
    {α : Type*} [Fintype α] [DecidableEq α]
    (κ δ : ℚ) (t : α → ℚ) (anchor : α) (hanchor : t anchor = 1)
    (hp_nonzero : ∀ x, diagonalStatistic κ t x ≠ 0)
    (hr_nonzero :
      ∀ x,
        pom_diagonal_rate_diagonal_determines_commute_refreshRate κ (diagonalStatistic κ t) x ≠ 0) :
    let p := diagonalStatistic κ t
    let π := diagonalStationary κ t
    let r := pom_diagonal_rate_diagonal_determines_commute_refreshRate κ p
    let S := pom_diagonal_rate_diagonal_determines_commute_normalizer π r
    κ = p anchor - 1 ∧
      (∀ x, t x = p anchor / p x) ∧
      (∀ x, π x = p x) ∧
      (∀ x y, diagonalKernel κ δ t x y = if x = y then p x else δ * π y) ∧
      (∀ x, r x = 1 - (κ / (1 + κ)) * p x) ∧
      ∀ x y, x ≠ y →
        pom_diagonal_rate_diagonal_determines_commute_commuteTime r π x y =
          S * (1 / π x + 1 / π y) := by
  dsimp
  have hdiag := paper_pom_diagonal_rate_diagonal_statistics_complete (α := α) κ δ t
  rcases hdiag with ⟨hp, _hanti, _hroot, _huniqRoot, _hξ, _hw, hπ, hp_eq_pi, hkernel⟩
  have hanchor_value : diagonalStatistic κ t anchor = 1 + κ := by
    simp [diagonalStatistic, hanchor]
  have hκ : κ = diagonalStatistic κ t anchor - 1 := by
    linarith [hanchor_value]
  have hrecover : ∀ x, t x = diagonalStatistic κ t anchor / diagonalStatistic κ t x := by
    intro x
    have htx : t x ≠ 0 := by
      intro htx0
      exact hp_nonzero x (by simp [diagonalStatistic, htx0])
    have hmul : t x * diagonalStatistic κ t x = 1 + κ := by
      rw [hp x]
      field_simp [htx]
    calc
      t x = (1 + κ) / diagonalStatistic κ t x := by
        exact (eq_div_iff (hp_nonzero x)).2 (by simpa [mul_comm] using hmul)
      _ = diagonalStatistic κ t anchor / diagonalStatistic κ t x := by
        simp [hanchor_value]
  have hπ_eq_p : ∀ x, diagonalStationary κ t x = diagonalStatistic κ t x := by
    intro x
    exact (hπ x).trans (hp_eq_pi x).symm
  refine ⟨hκ, hrecover, hπ_eq_p, hkernel, ?_, ?_⟩
  · intro x
    rfl
  · intro x y hxy
    let p : α → ℚ := diagonalStatistic κ t
    let π : α → ℚ := diagonalStationary κ t
    let r : α → ℚ := pom_diagonal_rate_diagonal_determines_commute_refreshRate κ p
    let S : ℚ := pom_diagonal_rate_diagonal_determines_commute_normalizer π r
    have hπx_ne : π x ≠ 0 := by
      dsimp [π, p]
      rw [hπ_eq_p x]
      exact hp_nonzero x
    have hπy_ne : π y ≠ 0 := by
      dsimp [π, p]
      rw [hπ_eq_p y]
      exact hp_nonzero y
    have hrx_ne : r x ≠ 0 := hr_nonzero x
    have hry_ne : r y ≠ 0 := hr_nonzero y
    have hxy_hit :
        diagonalRateAbsorbingMeanHitTime r π x y =
          1 / r x + (1 / π y) * (S - π y / r y) := by
      rw [paper_pom_diagonal_rate_refresh_hitting_time_mean_closed (r := r) (π := π) (x := x)
        (y := y)]
      rw [pom_diagonal_rate_diagonal_determines_commute_deleted_sum (π := π) (r := r) (y := y)]
    have hyx_hit :
        diagonalRateAbsorbingMeanHitTime r π y x =
          1 / r y + (1 / π x) * (S - π x / r x) := by
      rw [paper_pom_diagonal_rate_refresh_hitting_time_mean_closed (r := r) (π := π) (x := y)
        (y := x)]
      rw [pom_diagonal_rate_diagonal_determines_commute_deleted_sum (π := π) (r := r) (y := x)]
    dsimp [S, π, r, p] at hxy_hit hyx_hit hπx_ne hπy_ne hrx_ne hry_ne ⊢
    unfold pom_diagonal_rate_diagonal_determines_commute_commuteTime
    rw [hxy_hit, hyx_hit]
    field_simp [hπx_ne, hπy_ne, hrx_ne, hry_ne]
    ring_nf

end Omega.POM
