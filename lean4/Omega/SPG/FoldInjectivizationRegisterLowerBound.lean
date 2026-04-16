import Mathlib.Data.Nat.Log
import Omega.SPG.RegisterLowerBound
import Omega.Folding.FiberWeightCount

namespace Omega.SPG

/-- Any auxiliary register that makes the finite fold map injective must dominate the maximal fold
fiber, hence also the average compression ratio `2^m / |X_m|` and its base-2 bit budget.
    prop:spg-fold-injectivization-register-lower-bound -/
theorem paper_spg_fold_injectivization_register_lower_bound
    {R : Type} [Fintype R]
    (m : ℕ) (register : Omega.Word m → R)
    (hinj : Function.Injective fun ω => (Omega.Fold ω, register ω)) :
    Omega.X.maxFiberMultiplicity m ≤ Fintype.card R ∧
      2 ^ m ≤ Omega.X.maxFiberMultiplicity m * Nat.fib (m + 2) ∧
      2 ^ m ≤ Fintype.card R * Nat.fib (m + 2) ∧
      Nat.clog 2 (Omega.X.maxFiberMultiplicity m) ≤ Nat.clog 2 (Fintype.card R) := by
  obtain ⟨x, hx⟩ := Omega.X.maxFiberMultiplicity_achieved m
  have hfiber :
      Fintype.card {ω : Omega.Word m // Omega.Fold ω = x} ≤ Fintype.card R :=
    Omega.SPG.RegisterLowerBound.fiber_card_le_register_card Omega.Fold register hinj x
  have hcard :
      Fintype.card {ω : Omega.Word m // Omega.Fold ω = x} = Omega.X.fiberMultiplicity x := by
    rw [Omega.X.fiberMultiplicity]
    exact Fintype.card_of_subtype (Omega.X.fiber x) (fun ω => by
      simp [Omega.X.fiber])
  have hmax : Omega.X.maxFiberMultiplicity m ≤ Fintype.card R := by
    rw [← hx, ← hcard]
    exact hfiber
  have havg : 2 ^ m ≤ Omega.X.maxFiberMultiplicity m * Nat.fib (m + 2) :=
    Omega.pow_le_maxFiberMultiplicity_mul_fib m
  have hratio : 2 ^ m ≤ Fintype.card R * Nat.fib (m + 2) := by
    exact havg.trans (Nat.mul_le_mul_right _ hmax)
  have hclog :
      Nat.clog 2 (Omega.X.maxFiberMultiplicity m) ≤ Nat.clog 2 (Fintype.card R) :=
    Nat.clog_mono_right 2 hmax
  exact ⟨hmax, havg, hratio, hclog⟩

end Omega.SPG
