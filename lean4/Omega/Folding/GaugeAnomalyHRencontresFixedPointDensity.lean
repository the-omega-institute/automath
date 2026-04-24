import Mathlib.Tactic

namespace Omega.Folding

/-- Chapter-local derangement count seed. -/
def derangementCount : ℕ → ℕ
  | 0 => 1
  | 1 => 0
  | n + 2 => (n + 1) * (derangementCount n + derangementCount (n + 1))

/-- Density of permutations on `n` letters with exactly `r` fixed points. -/
def rencontresDensity (n r : ℕ) : ℚ :=
  if _ : r ≤ n then
    (Nat.choose n r : ℚ) * derangementCount (n - r) / n.factorial
  else
    0

/-- Joint density with the independent `P₁₀` irreducibility event of density `1 / 10`. -/
def jointIrreducibleRencontresDensity (n r : ℕ) : ℚ :=
  (1 / 10 : ℚ) * rencontresDensity n r

/-- Fixed-point rencontres density for the `S₁₉` factor, together with the `1 / 10` product-law
joint density coming from the independent `P₁₀` irreducibility event. -/
theorem paper_fold_gauge_anomaly_H_rencontres_fixed_point_density (r : ℕ) (hr : r ≤ 19) :
    let δr := rencontresDensity 19 r
    let joint := jointIrreducibleRencontresDensity 19 r
    δr = (Nat.choose 19 r : ℚ) * derangementCount (19 - r) / Nat.factorial 19 ∧
      joint = (1 / 10 : ℚ) * δr := by
  simp [rencontresDensity, jointIrreducibleRencontresDensity, hr]

end Omega.Folding
