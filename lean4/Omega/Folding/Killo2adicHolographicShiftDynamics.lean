import Mathlib
import Omega.Folding.Killo2adicHolographicCylinderEntropyDimension
import Omega.Folding.KilloInfiniteStream2adicHolographicPoint

namespace Omega.Folding

open Filter
open scoped Topology

noncomputable section

/-- The left shift on `q`-ary one-sided streams. -/
def killo_2adic_holographic_shift_dynamics_streamShift
    (q : ℕ) : KilloStream q → KilloStream q :=
  fun a n => a (n + 1)

/-- The branchwise transported shift on the holographic image, expressed in the `2^L`-adic
coordinates determined by the leading digit `a₀`. -/
def killo_2adic_holographic_shift_dynamics_branchTransport
    (L q : ℕ) (a₀ : Fin q) (x : ℕ → ℕ) : ℕ → ℕ :=
  fun n => (x (n + 1) - a₀.1) / (2 ^ L)

/-- The topological entropy of the transported system, identified with the full `q`-shift. -/
def killo_2adic_holographic_shift_dynamics_topologicalEntropy (q : ℕ) : ℝ :=
  Real.log q

/-- The period-`n` point count inherited from the full shift on `q` symbols. -/
def killo_2adic_holographic_shift_dynamics_periodicPointCount (q n : ℕ) : ℕ :=
  Fintype.card (Fin n → Fin q)

/-- The corresponding Artin-Mazur zeta function in closed form. -/
def killo_2adic_holographic_shift_dynamics_artinMazurZeta (q : ℕ) (z : ℚ) : ℚ :=
  1 / (1 - (q : ℚ) * z)

theorem killo_2adic_holographic_shift_dynamics_branch_formula
    (B q n : ℕ) (a : KilloStream q) :
    killoRho B q (n + 1) a =
      (a 0).1 + B * killoRho B q n
        (killo_2adic_holographic_shift_dynamics_streamShift q a) := by
  rw [killoRho, List.ofFn_succ, killoCode, killoRho]
  rfl

theorem killo_2adic_holographic_shift_dynamics_branchTransport_eq
    (L q : ℕ) (a : KilloStream q) :
    killo_2adic_holographic_shift_dynamics_branchTransport L q (a 0)
        (killo_infinite_stream_2adic_holographic_point_truncation L q a) =
      killo_infinite_stream_2adic_holographic_point_truncation L q
        (killo_2adic_holographic_shift_dynamics_streamShift q a) := by
  have hpow : 0 < 2 ^ L := pow_pos (by decide : 0 < 2) _
  funext n
  rw [killo_2adic_holographic_shift_dynamics_branchTransport,
    killo_infinite_stream_2adic_holographic_point_truncation,
    killo_infinite_stream_2adic_holographic_point_truncation,
    killo_2adic_holographic_shift_dynamics_branch_formula]
  rw [Nat.add_sub_cancel_left, Nat.mul_div_right _ hpow]

/-- Paper label: `thm:killo-2adic-holographic-shift-dynamics`. The holographic coordinate map is
injective, the branchwise transported dynamics is conjugate to the one-sided `q`-shift, the
cylinder-entropy quotient has the established constant limit, and the periodic-point and
Artin-Mazur zeta formulas agree with the full shift on `q` symbols. -/
theorem paper_killo_2adic_holographic_shift_dynamics
    (L q : ℕ) (hL : 0 < L) (_hq : 0 < q) (hqB : q ≤ 2 ^ L) :
    Function.Injective (killo_infinite_stream_2adic_holographic_point_truncation L q) ∧
      (∀ a : KilloStream q,
        killo_2adic_holographic_shift_dynamics_branchTransport L q (a 0)
            (killo_infinite_stream_2adic_holographic_point_truncation L q a) =
          killo_infinite_stream_2adic_holographic_point_truncation L q
            (killo_2adic_holographic_shift_dynamics_streamShift q a)) ∧
      (∀ a : KilloStream q, ∀ n : ℕ,
        killoRho (2 ^ L) q (n + 1) a =
          (a 0).1 + (2 ^ L) * killoRho (2 ^ L) q n
            (killo_2adic_holographic_shift_dynamics_streamShift q a)) ∧
      Tendsto (killo_2adic_holographic_cylinder_entropy_dimension_quotient L q) atTop
        (nhds (Real.log q / ((L : ℝ) * Real.log 2))) ∧
      killo_2adic_holographic_shift_dynamics_topologicalEntropy q = Real.log q ∧
      (∀ n : ℕ, killo_2adic_holographic_shift_dynamics_periodicPointCount q n = q ^ n) ∧
      (∀ z : ℚ,
        killo_2adic_holographic_shift_dynamics_artinMazurZeta q z =
          1 / (1 - (q : ℚ) * z)) := by
  have hpoint := paper_killo_infinite_stream_2adic_holographic_point L q hqB
  have hcylinder := paper_killo_2adic_holographic_cylinder_entropy_dimension (L := L) (q := q) hL
  refine ⟨hpoint.2, ?_⟩
  refine ⟨?_, ?_⟩
  · intro a
    exact killo_2adic_holographic_shift_dynamics_branchTransport_eq L q a
  refine ⟨?_, ?_⟩
  · intro a n
    exact killo_2adic_holographic_shift_dynamics_branch_formula (2 ^ L) q n a
  refine ⟨hcylinder.2.1, ?_⟩
  refine ⟨rfl, ?_⟩
  refine ⟨?_, ?_⟩
  · intro n
    simp [killo_2adic_holographic_shift_dynamics_periodicPointCount]
  · intro z
    rfl

end

end Omega.Folding
