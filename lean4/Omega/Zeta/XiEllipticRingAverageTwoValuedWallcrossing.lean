import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Partial sums of the wallcrossing jump masses. -/
noncomputable def xi_elliptic_ring_average_two_valued_wallcrossing_partialSum
    (jump : ℕ → ℂ) (j : ℕ) : ℂ :=
  Nat.rec 0 (fun n s => s + jump n) j

/-- Chamber value written as a base constant plus the cumulative jump mass. -/
noncomputable def xi_elliptic_ring_average_two_valued_wallcrossing_average
    (base : ℂ) (jump : ℕ → ℂ) (j : ℕ) : ℂ :=
  base + xi_elliptic_ring_average_two_valued_wallcrossing_partialSum jump j

/-- The chamber values use only the two distinguished levels `base` and `base + Δ`. -/
def xi_elliptic_ring_average_two_valued_wallcrossing_twoValuedUpTo
    (base Δ : ℂ) (jump : ℕ → ℂ) (N : ℕ) : Prop :=
  ∀ j ≤ N,
    xi_elliptic_ring_average_two_valued_wallcrossing_average base jump j = base ∨
      xi_elliptic_ring_average_two_valued_wallcrossing_average base jump j = base + Δ

/-- Equivalent partial-sum formulation of the two-valued condition. -/
def xi_elliptic_ring_average_two_valued_wallcrossing_partialTwoValuedUpTo
    (Δ : ℂ) (jump : ℕ → ℂ) (N : ℕ) : Prop :=
  ∀ j ≤ N,
    xi_elliptic_ring_average_two_valued_wallcrossing_partialSum jump j = 0 ∨
      xi_elliptic_ring_average_two_valued_wallcrossing_partialSum jump j = Δ

lemma xi_elliptic_ring_average_two_valued_wallcrossing_partialSum_succ
    (jump : ℕ → ℂ) (j : ℕ) :
    xi_elliptic_ring_average_two_valued_wallcrossing_partialSum jump (j + 1) =
      xi_elliptic_ring_average_two_valued_wallcrossing_partialSum jump j + jump j := by
  rfl

lemma xi_elliptic_ring_average_two_valued_wallcrossing_jump_eq_diff
    (jump : ℕ → ℂ) (j : ℕ) :
    jump j =
      xi_elliptic_ring_average_two_valued_wallcrossing_partialSum jump (j + 1) -
        xi_elliptic_ring_average_two_valued_wallcrossing_partialSum jump j := by
  rw [xi_elliptic_ring_average_two_valued_wallcrossing_partialSum_succ]
  ring

lemma xi_elliptic_ring_average_two_valued_wallcrossing_next_partial
    {Δ : ℂ} {jump : ℕ → ℂ} {N j : ℕ}
    (hpartial :
      xi_elliptic_ring_average_two_valued_wallcrossing_partialTwoValuedUpTo Δ jump (N + 1))
    (hj : j < N + 1) (hjump : jump j ≠ 0) :
    (xi_elliptic_ring_average_two_valued_wallcrossing_partialSum jump j = 0 ∧
        xi_elliptic_ring_average_two_valued_wallcrossing_partialSum jump (j + 1) = Δ) ∨
      (xi_elliptic_ring_average_two_valued_wallcrossing_partialSum jump j = Δ ∧
        xi_elliptic_ring_average_two_valued_wallcrossing_partialSum jump (j + 1) = 0) := by
  have hj0 := hpartial j (Nat.le_of_lt hj)
  have hj1 := hpartial (j + 1) (Nat.succ_le_of_lt hj)
  cases hj0 with
  | inl h0 =>
      cases hj1 with
      | inl h1 =>
          exfalso
          apply hjump
          simpa [h0, h1] using
            xi_elliptic_ring_average_two_valued_wallcrossing_jump_eq_diff jump j
      | inr h1 =>
          exact Or.inl ⟨h0, h1⟩
  | inr h0 =>
      cases hj1 with
      | inl h1 =>
          exact Or.inr ⟨h0, h1⟩
      | inr h1 =>
          exfalso
          apply hjump
          simpa [h0, h1] using
            xi_elliptic_ring_average_two_valued_wallcrossing_jump_eq_diff jump j

/-- Paper label: `thm:xi-elliptic-ring-average-two-valued-wallcrossing`. The elliptic ring
average is two-valued exactly when every cumulative jump mass lies in `{0, Δ}`; in that regime
each jump is a difference of consecutive partial sums, and every nonzero jump equals `±Δ`. -/
theorem paper_xi_elliptic_ring_average_two_valued_wallcrossing
    (base Δ : ℂ) (jump : ℕ → ℂ) (N : ℕ) :
    (xi_elliptic_ring_average_two_valued_wallcrossing_twoValuedUpTo base Δ jump N ↔
        xi_elliptic_ring_average_two_valued_wallcrossing_partialTwoValuedUpTo Δ jump N) ∧
      (xi_elliptic_ring_average_two_valued_wallcrossing_partialTwoValuedUpTo Δ jump (N + 1) →
        (∀ j < N + 1,
          jump j =
              xi_elliptic_ring_average_two_valued_wallcrossing_partialSum jump (j + 1) -
                xi_elliptic_ring_average_two_valued_wallcrossing_partialSum jump j ∧
            (jump j ≠ 0 → jump j = Δ ∨ jump j = -Δ))) := by
  refine ⟨?_, ?_⟩
  · constructor
    · intro htwo j hj
      rcases htwo j hj with hbase | hdelta
      · left
        have hsub := congrArg (fun z => z - base) hbase
        simpa [xi_elliptic_ring_average_two_valued_wallcrossing_average] using hsub
      · right
        have hsub := congrArg (fun z => z - base) hdelta
        simpa [xi_elliptic_ring_average_two_valued_wallcrossing_average] using hsub
    · intro hpartial j hj
      rcases hpartial j hj with hzero | hdelta
      · left
        simp [xi_elliptic_ring_average_two_valued_wallcrossing_average, hzero]
      · right
        simp [xi_elliptic_ring_average_two_valued_wallcrossing_average, hdelta]
  · intro hpartial
    intro j hj
    refine ⟨xi_elliptic_ring_average_two_valued_wallcrossing_jump_eq_diff jump j, ?_⟩
    intro hjump
    rcases
        xi_elliptic_ring_average_two_valued_wallcrossing_next_partial hpartial hj hjump with
      hstep | hstep
    · left
      rcases hstep with ⟨h0, h1⟩
      simpa [h0, h1] using
        xi_elliptic_ring_average_two_valued_wallcrossing_jump_eq_diff jump j
    · right
      rcases hstep with ⟨h0, h1⟩
      simpa [h0, h1] using
        xi_elliptic_ring_average_two_valued_wallcrossing_jump_eq_diff jump j

end Omega.Zeta
