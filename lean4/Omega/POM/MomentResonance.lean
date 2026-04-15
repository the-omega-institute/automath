import Mathlib.Tactic

namespace Omega.POM

set_option maxHeartbeats 400000 in
/-- Paper-facing resonance/register-savings wrapper: once an invertible coordinate change sends
    the last `Δ` coordinates of each visible moment vector to zero for all `m ≥ m₀`, the first
    `d` coordinates give a reduced register description and the last `Δ` coordinates become
    syndrome checks.
    cor:pom-resonance-register-savings -/
theorem paper_pom_resonance_register_savings
    (d Δ m0 : ℕ)
    (M : ℕ → Fin (d + Δ) → ℝ)
    (T : Matrix (Fin (d + Δ)) (Fin (d + Δ)) ℝ)
    (hInv : IsUnit T.det)
    (hTail : ∀ m ≥ m0, ∀ j : Fin Δ, (T.mulVec (M m)) (Fin.natAdd d j) = 0) :
    IsUnit T.det ∧
      ∃ reduced : ℕ → Fin d → ℝ,
        ∀ m ≥ m0,
          (∀ i : Fin d, reduced m i = (T.mulVec (M m)) (Fin.castAdd Δ i)) ∧
            (∀ j : Fin Δ, (T.mulVec (M m)) (Fin.natAdd d j) = 0) := by
  refine ⟨hInv, ?_⟩
  refine ⟨fun m i => (T.mulVec (M m)) (Fin.castAdd Δ i), ?_⟩
  intro m hm
  refine ⟨?_, hTail m hm⟩
  intro i
  rfl

set_option maxHeartbeats 400000 in
/-- Paper-facing resonance theorem: an invertible coordinate change whose tail coordinates vanish
    yields a genuine nontrivial linear constraint on the original moment vectors.
    thm:pom-moment-resonance -/
theorem paper_pom_moment_resonance
    (d Delta m0 : ℕ)
    (M : ℕ → Fin (d + Delta) → ℝ)
    (T : Matrix (Fin (d + Delta)) (Fin (d + Delta)) ℝ)
    (hInv : IsUnit T.det)
    (hDelta : 0 < Delta)
    (hTail : ∀ m ≥ m0, ∀ j : Fin Delta, (T.mulVec (M m)) (Fin.natAdd d j) = 0) :
    ∃ alpha : Fin (d + Delta) → ℝ, alpha ≠ 0 ∧ ∀ m ≥ m0, (∑ i, alpha i * M m i) = 0 := by
  let j : Fin Delta := ⟨0, hDelta⟩
  let k : Fin (d + Delta) := Fin.natAdd d j
  refine ⟨fun i => T k i, ?_, ?_⟩
  · intro hAlpha
    have hrow : ∀ i, T k i = 0 := by
      intro i
      exact congrFun hAlpha i
    have hdet0 : T.det = 0 := Matrix.det_eq_zero_of_row_eq_zero k hrow
    exact (isUnit_iff_ne_zero.mp hInv) hdet0
  · intro m hm
    have hkm : (T.mulVec (M m)) k = 0 := hTail m hm j
    simpa [k, Matrix.mulVec, dotProduct]
      using hkm

end Omega.POM
