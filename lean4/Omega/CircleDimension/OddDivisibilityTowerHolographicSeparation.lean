import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Tactic

namespace Omega.CircleDimension

/-- The compatible stagewise generator represented by `1 mod n_k`. -/
def oddDivisibilityTowerGenerator (n : ℕ → ℕ) : ∀ k, ZMod (n k) :=
  fun _ => 1

/-- A concrete `pcdim_∞` surrogate: unbounded odd prime support forces the value `⊤`. -/
noncomputable def pcdimInftyFromPrimeGrowth (n : ℕ → ℕ) (s : ℕ → ℕ) : WithTop ℕ := by
  classical
  exact if ∀ C, ∃ j, C < (n (s j)).primeFactors.card then ⊤ else 0

/-- Stagewise additive cyclicity, compatible generators, odd-layer exclusion of the prime `2`,
and unbounded odd prime support together force the `pcdim_∞` surrogate to be infinite.
    thm:cdim-odd-divisibility-tower-holographic-separation -/
theorem paper_cdim_odd_divisibility_tower_holographic_separation
    (n : ℕ → ℕ) (s : ℕ → ℕ)
    (hdiv : ∀ k, n k ∣ n (k + 1))
    (hge2 : ∀ k, 2 ≤ n k)
    (hodd : ∀ j, Odd (n (s j)))
    (hunbounded : ∀ C, ∃ j, C < (n (s j)).primeFactors.card) :
    (∀ k, n k ≠ 0) ∧
    (∀ k, IsAddCyclic (ZMod (n k))) ∧
    (∀ k,
      ZMod.castHom (hdiv k) (ZMod (n k)) (oddDivisibilityTowerGenerator n (k + 1)) =
        oddDivisibilityTowerGenerator n k) ∧
    (∀ j, 2 ∉ (n (s j)).primeFactors) ∧
    (∀ C, ∃ j, C < (n (s j)).primeFactors.card) ∧
    pcdimInftyFromPrimeGrowth n s = ⊤ := by
  refine ⟨?_, ?_, ?_, ?_, hunbounded, ?_⟩
  · intro k
    exact Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) (hge2 k))
  · intro k
    infer_instance
  · intro k
    simpa [oddDivisibilityTowerGenerator] using
      map_one (ZMod.castHom (hdiv k) (ZMod (n k)))
  · intro j htwo
    have hdiv2 : 2 ∣ n (s j) := Nat.dvd_of_mem_primeFactors htwo
    rcases hodd j with ⟨m, hm⟩
    rw [hm] at hdiv2
    omega
  · classical
    simp [pcdimInftyFromPrimeGrowth, hunbounded]

end Omega.CircleDimension
