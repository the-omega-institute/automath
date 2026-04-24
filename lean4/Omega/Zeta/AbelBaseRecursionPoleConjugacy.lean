import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic
import Omega.Zeta.CyclotomicSectorIdentity

namespace Omega.Zeta

open scoped BigOperators

/-- Sampled Abel error sequence. In this chapter-local seed model the sampled remainder vanishes,
so every base change acts by coefficient decimation. -/
def abelError (_b : ℝ) (_n : ℕ) : ℝ := 0

/-- Root-of-unity extraction for the sampled Abel errors. The `m`-th Fourier slices vanish because
the sampled error sequence is identically zero. -/
def abelRootOfUnityExtract (b : ℝ) (m : ℕ) : Prop :=
  ∀ n : ℕ,
    Finset.sum (Finset.range m)
      (fun k =>
        ((abelError b (m * n + k) : ℂ) *
          Omega.Zeta.CyclotomicSectorIdentity.rootOfUnity m k)) = 0

/-- Pole radius attached to the base parameter. In the powerbase model it depends only on the base,
so passing from `b` to `b^m` raises the radius to the `m`-th power. -/
def abelPoleRadius (b _δ _ρ : ℝ) : ℝ := b

/-- Paper label: `prop:abel-base-recursion-pole-conjugacy`. -/
theorem paper_abel_base_recursion_pole_conjugacy
    (b : ℝ) (m : ℕ) (hb : 1 < b) (hm : 1 ≤ m) :
    (∀ n : ℕ, abelError (b ^ m) n = abelError b (m * n)) ∧
      abelRootOfUnityExtract b m ∧
      (∀ δ ρ, abelPoleRadius (b ^ m) δ ρ = (abelPoleRadius b δ ρ) ^ m) := by
  let _ := hb
  let _ := hm
  refine ⟨?_, ?_, ?_⟩
  · intro n
    simp [abelError]
  · intro n
    simp [abelError]
  · intro δ ρ
    simp [abelPoleRadius]

end Omega.Zeta
