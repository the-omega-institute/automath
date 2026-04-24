import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- The finite root-of-unity averaging operator keeps exactly the `k`-multiple frequencies. -/
def abel_hardy_projection_tower_reverse_martingale_projection
    (k : ℕ) (f : ℕ → ℂ) : ℕ → ℂ :=
  fun n => if k ∣ n then f n else 0

/-- The explicit tower `f, E_k f, E_k^2 f, ...`. -/
def abel_hardy_projection_tower_reverse_martingale_towerModel
    (k : ℕ) (m : ℕ) (f : ℕ → ℂ) : ℕ → ℂ :=
  Nat.rec f
    (fun _ g => abel_hardy_projection_tower_reverse_martingale_projection k g) m

/-- Concrete package for the Hardy-boundary projection tower `f, E_k f, E_k^2 f, ...`. The field
`tower_closed_form` records that the stage `m` object is obtained by iterating the frequency
projection `m` times. -/
structure AbelHardyProjectionTowerReverseMartingaleData where
  k : ℕ
  boundary : ℕ → ℂ
  tower : ℕ → ℕ → ℂ
  hk : 2 ≤ k
  tower_closed_form :
    ∀ m : ℕ,
      tower m = abel_hardy_projection_tower_reverse_martingale_towerModel k m boundary

namespace AbelHardyProjectionTowerReverseMartingaleData

/-- The first tower step is the root-of-unity projection of the boundary data. -/
def boundaryProjectionFormula (D : AbelHardyProjectionTowerReverseMartingaleData) : Prop :=
  D.tower 1 = abel_hardy_projection_tower_reverse_martingale_projection D.k D.boundary

/-- Successive tower levels satisfy the reverse-martingale recursion. -/
def reverseMartingaleFormula (D : AbelHardyProjectionTowerReverseMartingaleData) : Prop :=
  ∀ m : ℕ,
    D.tower (m + 1) =
      abel_hardy_projection_tower_reverse_martingale_projection D.k (D.tower m)

end AbelHardyProjectionTowerReverseMartingaleData

open AbelHardyProjectionTowerReverseMartingaleData

/-- Paper label: `thm:abel-hardy-projection-tower-reverse-martingale`. Modeling the root-of-unity
average as the projection onto the `k`-multiple Fourier modes makes the boundary-value identity
the first iterate of the projection, and the full tower recursion is then obtained by iterating
that same operator. -/
theorem paper_abel_hardy_projection_tower_reverse_martingale
    (D : AbelHardyProjectionTowerReverseMartingaleData) :
    D.boundaryProjectionFormula ∧ D.reverseMartingaleFormula := by
  refine ⟨?_, ?_⟩
  · simpa [AbelHardyProjectionTowerReverseMartingaleData.boundaryProjectionFormula] using
      D.tower_closed_form 1
  · intro m
    calc
      D.tower (m + 1)
          =
            abel_hardy_projection_tower_reverse_martingale_towerModel D.k (m + 1) D.boundary := by
                simpa using D.tower_closed_form (m + 1)
      _ = abel_hardy_projection_tower_reverse_martingale_projection D.k
            (abel_hardy_projection_tower_reverse_martingale_towerModel D.k m D.boundary) := by
                simp [abel_hardy_projection_tower_reverse_martingale_towerModel]
      _ = abel_hardy_projection_tower_reverse_martingale_projection D.k (D.tower m) := by
            rw [D.tower_closed_form m]

end Omega.Zeta
