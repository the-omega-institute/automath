import Mathlib.Tactic
import Omega.POM.DiagonalRateKeepResampleChannel

namespace Omega.POM

open scoped BigOperators

/-- The normalizing mass `A = ∑_z u_z`. -/
def pom_diagonal_rate_rank_one_refresh_decomposition_totalMass {α : Type*} [Fintype α]
    (u : α → ℝ) : ℝ :=
  ∑ z, u z

/-- The state-dependent refresh rate in the rank-one refresh decomposition. -/
noncomputable def pom_diagonal_rate_rank_one_refresh_decomposition_refreshRate {α : Type*}
    [Fintype α]
    (u : α → ℝ) (κ : ℝ) (x : α) : ℝ :=
  pom_diagonal_rate_rank_one_refresh_decomposition_totalMass u /
    (pom_diagonal_rate_rank_one_refresh_decomposition_totalMass u + κ * u x)

/-- The stationary law used by the rank-one refresh decomposition. -/
noncomputable def pom_diagonal_rate_rank_one_refresh_decomposition_stationaryLaw {α : Type*}
    [Fintype α]
    (u : α → ℝ) (y : α) : ℝ :=
  u y / pom_diagonal_rate_rank_one_refresh_decomposition_totalMass u

/-- The kernel written in the explicit `u`-`κ` coordinates from the paper. -/
noncomputable def pom_diagonal_rate_rank_one_refresh_decomposition_kernel {α : Type*} [Fintype α]
    [DecidableEq α] (u : α → ℝ) (κ : ℝ) (x y : α) : ℝ :=
  if y = x then
    ((1 + κ) * u x) /
      (pom_diagonal_rate_rank_one_refresh_decomposition_totalMass u + κ * u x)
  else
    u y / (pom_diagonal_rate_rank_one_refresh_decomposition_totalMass u + κ * u x)

/-- The diagonal part `diag(1 - r_δ)` of the kernel decomposition. -/
noncomputable def pom_diagonal_rate_rank_one_refresh_decomposition_diagonalPart {α : Type*}
    [Fintype α]
    [DecidableEq α] (u : α → ℝ) (κ : ℝ) (x y : α) : ℝ :=
  if y = x then 1 - pom_diagonal_rate_rank_one_refresh_decomposition_refreshRate u κ x else 0

/-- The rank-one refresh part `r_δ π_δᵀ` of the kernel decomposition. -/
noncomputable def pom_diagonal_rate_rank_one_refresh_decomposition_refreshPart {α : Type*}
    [Fintype α]
    (u : α → ℝ) (κ : ℝ) (x y : α) : ℝ :=
  pom_diagonal_rate_rank_one_refresh_decomposition_refreshRate u κ x *
    pom_diagonal_rate_rank_one_refresh_decomposition_stationaryLaw u y

/-- Paper label: `prop:pom-diagonal-rate-rank-one-refresh-decomposition`. The keep-resample
kernel rewrites as a state-dependent diagonal hold plus a rank-one global refresh term. -/
theorem paper_pom_diagonal_rate_rank_one_refresh_decomposition
    {α : Type*} [Fintype α] [DecidableEq α] (u : α → ℝ) (κ : ℝ)
    (hmass_ne : pom_diagonal_rate_rank_one_refresh_decomposition_totalMass u ≠ 0)
    (hdenom :
      ∀ x : α,
        pom_diagonal_rate_rank_one_refresh_decomposition_totalMass u + κ * u x ≠ 0) :
    (∀ x y : α, y ≠ x →
      pom_diagonal_rate_rank_one_refresh_decomposition_kernel u κ x y =
        pom_diagonal_rate_rank_one_refresh_decomposition_refreshPart u κ x y) ∧
      (∀ x : α,
        pom_diagonal_rate_rank_one_refresh_decomposition_kernel u κ x x =
          pom_diagonal_rate_rank_one_refresh_decomposition_refreshPart u κ x x +
            (1 - pom_diagonal_rate_rank_one_refresh_decomposition_refreshRate u κ x)) ∧
      (∀ x y : α,
        pom_diagonal_rate_rank_one_refresh_decomposition_kernel u κ x y =
          pom_diagonal_rate_rank_one_refresh_decomposition_diagonalPart u κ x y +
            pom_diagonal_rate_rank_one_refresh_decomposition_refreshPart u κ x y) ∧
      pom_diagonal_rate_rank_one_refresh_decomposition_kernel u κ =
        fun x y =>
          pom_diagonal_rate_rank_one_refresh_decomposition_diagonalPart u κ x y +
            pom_diagonal_rate_rank_one_refresh_decomposition_refreshPart u κ x y := by
  have hOff :
      ∀ x y : α, y ≠ x →
        pom_diagonal_rate_rank_one_refresh_decomposition_kernel u κ x y =
          pom_diagonal_rate_rank_one_refresh_decomposition_refreshPart u κ x y := by
    intro x y hxy
    unfold pom_diagonal_rate_rank_one_refresh_decomposition_kernel
    unfold pom_diagonal_rate_rank_one_refresh_decomposition_refreshPart
    unfold pom_diagonal_rate_rank_one_refresh_decomposition_refreshRate
    unfold pom_diagonal_rate_rank_one_refresh_decomposition_stationaryLaw
    simp [hxy]
    field_simp [hmass_ne, hdenom x]
  have hDiag :
      ∀ x : α,
        pom_diagonal_rate_rank_one_refresh_decomposition_kernel u κ x x =
          pom_diagonal_rate_rank_one_refresh_decomposition_refreshPart u κ x x +
            (1 - pom_diagonal_rate_rank_one_refresh_decomposition_refreshRate u κ x) := by
    intro x
    unfold pom_diagonal_rate_rank_one_refresh_decomposition_kernel
    unfold pom_diagonal_rate_rank_one_refresh_decomposition_refreshPart
    unfold pom_diagonal_rate_rank_one_refresh_decomposition_refreshRate
    unfold pom_diagonal_rate_rank_one_refresh_decomposition_stationaryLaw
    simp
    field_simp [hmass_ne, hdenom x]
    ring_nf
  have hPointwise :
      ∀ x y : α,
        pom_diagonal_rate_rank_one_refresh_decomposition_kernel u κ x y =
          pom_diagonal_rate_rank_one_refresh_decomposition_diagonalPart u κ x y +
            pom_diagonal_rate_rank_one_refresh_decomposition_refreshPart u κ x y := by
    intro x y
    by_cases hxy : y = x
    · subst y
      simpa [pom_diagonal_rate_rank_one_refresh_decomposition_diagonalPart, add_comm] using hDiag x
    · have hOffxy := hOff x y hxy
      simpa [pom_diagonal_rate_rank_one_refresh_decomposition_diagonalPart, hxy] using hOffxy
  refine ⟨hOff, ?_⟩
  refine ⟨hDiag, ?_⟩
  refine ⟨hPointwise, ?_⟩
  funext x y
  exact hPointwise x y

end Omega.POM
