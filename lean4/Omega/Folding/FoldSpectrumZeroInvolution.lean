import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

namespace Omega.Folding

open scoped BigOperators

/-- The one-coordinate phase factor used in the concrete fold-spectrum model. -/
def foldSpectrumCoordinateFactor (_m k j : ℕ) : ℚ :=
  if (j + k) % 2 = 0 then (-1 : ℚ) else 1

/-- The `j`-th factor is a zero-producing factor exactly when it equals `-1`. -/
def foldSpectrumZeroFactor (m k j : ℕ) : Prop :=
  foldSpectrumCoordinateFactor m k j = -1

/-- The fold-spectrum summand is the product of the active one-coordinate factors. -/
def foldSpectrumTerm (m k : ℕ) (ω : Fin m → Bool) : ℚ :=
  ∏ i : Fin m, if ω i then foldSpectrumCoordinateFactor m k i.1 else 1

private lemma foldSpectrumTerm_flip_eq_neg (m k : ℕ) (j : Fin m)
    (hzero : foldSpectrumZeroFactor m k j.1) (ω : Fin m → Bool) :
    foldSpectrumTerm m k (Function.update ω j (!(ω j))) = -foldSpectrumTerm m k ω := by
  unfold foldSpectrumTerm
  have hj : j ∈ (Finset.univ : Finset (Fin m)) := Finset.mem_univ j
  rw [Finset.prod_eq_mul_prod_diff_singleton hj, Finset.prod_eq_mul_prod_diff_singleton hj]
  have hrest :
      ∏ i ∈ Finset.univ \ {j},
          (if Function.update ω j (!(ω j)) i then foldSpectrumCoordinateFactor m k i.1 else 1) =
        ∏ i ∈ Finset.univ \ {j},
          (if ω i then foldSpectrumCoordinateFactor m k i.1 else 1) := by
    refine Finset.prod_congr rfl ?_
    intro i hi
    have hij : i ≠ j := by
      simpa [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_singleton] using hi
    simp [Function.update_of_ne hij]
  rw [hrest]
  have hfactor : foldSpectrumCoordinateFactor m k j.1 = (-1 : ℚ) := hzero
  by_cases hω : ω j
  · simp [Function.update_self, hω, hfactor]
  · simp [Function.update_self, hω, hfactor]

/-- Flipping the `j`-th bit is a fixed-point-free involution; when the corresponding coordinate
factor equals `-1`, the paired fold-spectrum summands cancel exactly.
    cor:fold-spectrum-zero-involution -/
theorem paper_fold_spectrum_zero_involution (m k j : ℕ) (hj : j < m)
    (hzero : foldSpectrumZeroFactor m k j) :
    ∃ ι : (Fin m → Bool) → (Fin m → Bool),
      Function.Involutive ι ∧ (∀ ω, ι ω ≠ ω) ∧
        ∀ ω, foldSpectrumTerm m k ω + foldSpectrumTerm m k (ι ω) = 0 := by
  let jFin : Fin m := ⟨j, hj⟩
  refine ⟨fun ω => Function.update ω jFin (!(ω jFin)), ?_, ?_, ?_⟩
  · intro ω
    funext i
    by_cases hi : i = jFin
    · subst hi
      simp [Function.update_self]
    · simp [Function.update_of_ne hi]
  · intro ω hfix
    have hbit := congrArg (fun f => f jFin) hfix
    cases hω : ω jFin <;> simp [Function.update_self, hω] at hbit
  · intro ω
    have hflip :
        foldSpectrumTerm m k (Function.update ω jFin (!(ω jFin))) = -foldSpectrumTerm m k ω :=
      foldSpectrumTerm_flip_eq_neg m k jFin hzero ω
    calc
      foldSpectrumTerm m k ω + foldSpectrumTerm m k (Function.update ω jFin (!(ω jFin)))
          = foldSpectrumTerm m k ω + (-foldSpectrumTerm m k ω) := by rw [hflip]
      _ = 0 := by ring

end Omega.Folding
