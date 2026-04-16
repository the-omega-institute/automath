import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Omega.EA.FibAdicTower

namespace Omega.EA

open FibAdicTower

/-- The quotient map in the Fibonacci divisibility tower. -/
noncomputable def fibAdicQuotientMap (k : ℕ) :
    ZMod (M_k (k + 1)) →+* ZMod (M_k k) :=
  ZMod.castHom (M_k_dvd_succ k) (ZMod (M_k k))

/-- Compatible sequences over the Fibonacci divisibility tower. -/
def FibAdicCompatibleSeq :=
  {x : (k : ℕ) → ZMod (M_k k) // ∀ k, fibAdicQuotientMap k (x (k + 1)) = x k}

/-- Coordinate projection from the inverse-limit seed. -/
def fibAdicProjection (k : ℕ) (x : FibAdicCompatibleSeq) : ZMod (M_k k) := x.1 k

/-- Coordinatewise unit-compatible inverse-limit points. -/
def FibAdicUnitLimit :=
  {x : FibAdicCompatibleSeq // ∀ k, IsUnit (fibAdicProjection k x)}

/-- Seed profinite-completeness package: a nonempty compatible inverse limit built from finite
layers. -/
def fibAdicProfiniteComplete : Prop :=
  Nonempty FibAdicCompatibleSeq ∧ ∀ k, Finite (ZMod (M_k k))

/-- Seed finite-quotient package: every coordinate projection is surjective and respects the
tower compatibility map. -/
def fibAdicFiniteQuotientCompatibility : Prop :=
  ∀ k, Function.Surjective (fibAdicQuotientMap k)

/-- Seed unit-limit package: coordinatewise units are exactly the data needed to land in the
inverse-limit unit object. -/
def fibAdicUnitGroupLimit : Prop :=
  ∀ x : FibAdicCompatibleSeq, (∀ k, IsUnit (fibAdicProjection k x)) → ∃ u : FibAdicUnitLimit, u.1 = x

private theorem M_k_pos (k : ℕ) : 0 < M_k k := by
  unfold M_k n_k
  exact Nat.fib_pos.mpr (pow_pos (by decide : 0 < 2) _)

theorem paper_fib_adic_basic :
    fibAdicProfiniteComplete ∧ fibAdicFiniteQuotientCompatibility ∧ fibAdicUnitGroupLimit := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · refine ⟨⟨fun k => (0 : ZMod (M_k k)), ?_⟩⟩
      intro k
      simp [fibAdicQuotientMap]
    · intro k
      haveI : NeZero (M_k k) := ⟨Nat.ne_of_gt (M_k_pos k)⟩
      exact Finite.of_fintype (ZMod (M_k k))
  · intro k
    simpa [fibAdicQuotientMap] using ZMod.castHom_surjective (M_k_dvd_succ k)
  · intro x hx
    exact ⟨⟨x, hx⟩, rfl⟩

end Omega.EA
