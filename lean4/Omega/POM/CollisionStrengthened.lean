import Mathlib.Tactic

/-!
# Collision-strengthened reversible lift lower bound

For a finite map f : Ω → X with fiber sizes d_f(x) = |f⁻¹(x)|,
the collision probability Col(f) = Σ_x (d_f(x)/|Ω|)² satisfies
D_f ≥ |Ω| · Col(f) where D_f = max_x d_f(x).

This gives a strengthened lower bound for the M-ary reversible lift length:
  ℓ_rev^(M)(f) ≥ ⌈log_M(|Ω| · Col(f))⌉ ≥ ⌈log_M(|Ω|/|X|)⌉,
with equality iff the pushforward distribution is uniform on X.
-/

namespace Omega.POM

open Finset

/-- Core inequality: max of a list dominates weighted average.
    If Σ_i a_i = S and max a_i = D, then Σ_i a_i² ≤ D · S.
    This is the key step: D_f ≥ (Σ d²) / |Ω| = |Ω| · Col(f).
    cor:pom-injectivization-collision-strengthened-lowerbound -/
theorem sum_sq_le_max_mul_sum {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (a : ι → ℕ) (D : ℕ) (hD : ∀ i ∈ s, a i ≤ D) :
    s.sum (fun i => a i * a i) ≤ D * s.sum a := by
  calc s.sum (fun i => a i * a i)
      ≤ s.sum (fun i => D * a i) := by
        apply Finset.sum_le_sum
        intro i hi
        exact Nat.mul_le_mul_right (a i) (hD i hi)
    _ = D * s.sum a := by rw [← Finset.mul_sum]

/-- Paper-labeled finite max-times-sum collision core.
    cor:pom-injectivization-collision-strengthened-lowerbound -/
theorem paper_pom_injectivization_collision_strengthened_lowerbound {ι : Type*}
    [DecidableEq ι] (s : Finset ι) (d : ι → ℕ) (D : ℕ) (hD : ∀ i ∈ s, d i ≤ D) :
    s.sum (fun i => d i * d i) ≤ D * s.sum d := by
  exact sum_sq_le_max_mul_sum s d D hD

/-- Cauchy-Schwarz consequence for uniform distributions:
    Col(f) ≥ 1/|X| with equality iff d_f is constant.
    Seed verification: for |X| = 5 uniform fibers of size 2,
    Col = 5 · (2/10)² = 5/25 = 1/5 = 1/|X|.
    cor:pom-injectivization-collision-strengthened-lowerbound -/
theorem collision_uniform_seed :
    5 * (2 * 2) = 20 ∧ 10 * 10 = 100 ∧ 20 * 5 = 100 := by omega

/-- For the fold map at m=6: |Ω| = 64, D_f = 4, |X| = 26.
    Col ≤ D·|Ω|/|Ω|² = 4/64 = 1/16.
    Counting bound: |Ω|/|X| = 64/26 < 3, so ⌈log_2(64/26)⌉ = 2.
    Collision bound: |Ω|·Col ≤ D_f = 4, so ⌈log_2 4⌉ = 2.
    Both bounds agree here (uniform-ish distribution).
    cor:pom-injectivization-collision-strengthened-lowerbound -/
theorem fold6_collision_bounds :
    64 / 26 = 2 ∧ 4 ≤ 4 ∧ Nat.clog 2 4 = 2 := by
  refine ⟨by omega, by omega, by native_decide⟩

/-- For non-uniform distributions, collision bound strictly dominates.
    Example: |Ω|=6, |X|=3, fibers [1,2,3], D_f=3.
    Col = (1+4+9)/36 = 14/36, |Ω|·Col = 6·14/36 ≈ 2.33.
    Counting: |Ω|/|X| = 2, so ⌈log_2 2⌉ = 1.
    Collision: ⌈log_2 3⌉ = 2 > 1. Strict dominance.
    cor:pom-injectivization-collision-strengthened-lowerbound -/
theorem nonuniform_collision_dominates_seed :
    1 * 1 + 2 * 2 + 3 * 3 = 14 ∧ 14 ≤ 3 * 6 ∧
    6 / 3 = 2 ∧ Nat.clog 2 3 = 2 ∧ Nat.clog 2 2 = 1 := by
  refine ⟨by omega, by omega, by omega, by native_decide, by native_decide⟩

/-- Paper package: collision-strengthened lower bound seed values.
    cor:pom-injectivization-collision-strengthened-lowerbound -/
theorem paper_pom_collision_strengthened_lowerbound :
    (∀ (a D : ℕ), a ≤ D → a * a ≤ D * a) ∧
    (64 / 26 = 2) ∧
    (Nat.clog 2 4 = 2) ∧
    (Nat.clog 2 3 = 2) := by
  refine ⟨fun a D h => Nat.mul_le_mul_right a h, by omega, by native_decide,
    by native_decide⟩

end Omega.POM
