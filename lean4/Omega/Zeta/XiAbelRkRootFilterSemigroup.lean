import Mathlib.Data.Complex.Basic

namespace Omega.Zeta

/-- Extract the subsequence indexed by the `k`-th arithmetic progression. -/
def xi_abel_rk_root_filter_semigroup_extract (a : ℕ → ℂ) (k : ℕ) : ℕ → ℂ :=
  fun n => a (k * n)

/-- Paper label: `prop:xi-abel-Rk-root-filter-semigroup`.
Composing two coefficient extractors multiplies their step sizes. -/
theorem paper_xi_abel_rk_root_filter_semigroup (a : ℕ → ℂ) (k l : ℕ) (hk : 2 ≤ k)
    (hl : 2 ≤ l) :
    xi_abel_rk_root_filter_semigroup_extract
        (xi_abel_rk_root_filter_semigroup_extract a l) k =
      xi_abel_rk_root_filter_semigroup_extract a (k * l) := by
  let _ := hk
  let _ := hl
  funext n
  simp [xi_abel_rk_root_filter_semigroup_extract, Nat.mul_comm, Nat.mul_left_comm]

end Omega.Zeta
