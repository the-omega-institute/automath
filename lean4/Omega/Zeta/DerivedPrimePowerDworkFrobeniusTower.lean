import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete data for a prime-power Dwork tower. Each new level differs from the previous one by
an explicit `p^(k+1)` correction. -/
structure DerivedPrimePowerDworkFrobeniusTowerData where
  p : ℕ
  hp : 2 ≤ p
  seed : ℕ
  correction : ℕ → ℕ

namespace DerivedPrimePowerDworkFrobeniusTowerData

/-- The prime-power Dwork tower obtained by adding a `p^(k+1)` correction at level `k + 1`. -/
def tower (D : DerivedPrimePowerDworkFrobeniusTowerData) : ℕ → ℕ
  | 0 => D.seed
  | k + 1 => D.tower k + D.p ^ (k + 1) * D.correction k

lemma tower_zero (D : DerivedPrimePowerDworkFrobeniusTowerData) : D.tower 0 = D.seed := rfl

lemma tower_succ (D : DerivedPrimePowerDworkFrobeniusTowerData) (k : ℕ) :
    D.tower (k + 1) = D.tower k + D.p ^ (k + 1) * D.correction k := by
  rfl

/-- Integral Dwork congruence at every prime-power stage. -/
def integralCongruenceLaw (D : DerivedPrimePowerDworkFrobeniusTowerData) : Prop :=
  ∀ k : ℕ, D.tower (k + 1) = D.tower k + D.p ^ (k + 1) * D.correction k

/-- Modulo `p`, the whole prime-power tower collapses to the seed level. -/
def modpFrobeniusCollapseLaw (D : DerivedPrimePowerDworkFrobeniusTowerData) : Prop :=
  ∀ k : ℕ, D.tower k % D.p = D.seed % D.p

end DerivedPrimePowerDworkFrobeniusTowerData

open DerivedPrimePowerDworkFrobeniusTowerData

/-- Paper label: `thm:derived-prime-power-dwork-frobenius-tower`. The tower keeps the exact
`p^(k+1)` Dwork correction integrally, and modulo `p` every stage collapses to the seed by
induction on the level. -/
theorem paper_derived_prime_power_dwork_frobenius_tower
    (D : DerivedPrimePowerDworkFrobeniusTowerData) :
    D.integralCongruenceLaw ∧ D.modpFrobeniusCollapseLaw := by
  refine ⟨?_, ?_⟩
  · intro k
    exact D.tower_succ k
  · intro k
    induction k with
    | zero =>
        simp [DerivedPrimePowerDworkFrobeniusTowerData.tower_zero]
    | succ k ih =>
        rw [D.tower_succ, Nat.add_mod, ih]
        have hdiv : D.p ∣ D.p ^ (k + 1) * D.correction k := by
          exact dvd_mul_of_dvd_left (dvd_pow_self D.p (Nat.succ_ne_zero k)) (D.correction k)
        rw [Nat.mod_eq_zero_of_dvd hdiv]
        simp

end Omega.Zeta
