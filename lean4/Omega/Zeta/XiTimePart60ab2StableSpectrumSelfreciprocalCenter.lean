import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

private lemma xi_time_part60ab2_stable_spectrum_selfreciprocal_center_sum_complement
    (m : ℕ) (S : Finset ℕ) (hS : S ⊆ Finset.range m) :
    let M : ℕ := Nat.fib (m + 2)
    let A : Finset ℕ := Finset.range m
    let w : ℕ → ℕ := fun j => Nat.fib (j + 2)
    (((A \ S).sum w : ℕ) : ZMod M) =
      ((A.sum w : ℕ) : ZMod M) - ((S.sum w : ℕ) : ZMod M) := by
  dsimp
  let A : Finset ℕ := Finset.range m
  let w : ℕ → ℕ := fun j => Nat.fib (j + 2)
  have hsum_nat : (A \ S).sum w + S.sum w = A.sum w := by
    simpa [A, w] using (Finset.sum_sdiff hS (f := w))
  have hsum_z :
      (((A \ S).sum w : ℕ) : ZMod (Nat.fib (m + 2))) +
          ((S.sum w : ℕ) : ZMod (Nat.fib (m + 2))) =
        ((A.sum w : ℕ) : ZMod (Nat.fib (m + 2))) := by
    rw [← Nat.cast_add, hsum_nat]
  rw [← hsum_z]
  abel

private lemma xi_time_part60ab2_stable_spectrum_selfreciprocal_center_complement_complement
    {A S : Finset ℕ} (hS : S ⊆ A) : A \ (A \ S) = S := by
  ext x
  by_cases hxA : x ∈ A
  · by_cases hxS : x ∈ S <;> simp [hxA, hxS]
  · have hxS : x ∉ S := fun hx => hxA (hS hx)
    simp [hxA, hxS]

/-- Paper label: `thm:xi-time-part60ab2-stable-spectrum-selfreciprocal-center`. -/
theorem paper_xi_time_part60ab2_stable_spectrum_selfreciprocal_center (m : ℕ) :
    let M : ℕ := Nat.fib (m + 2)
    let Sigma : ℕ := (Finset.range m).sum (fun j => Nat.fib (j + 2))
    ∀ r : ZMod M,
      ((Finset.powerset (Finset.range m)).filter
          (fun S =>
            ((S.sum (fun j => Nat.fib (j + 2)) : ℕ) : ZMod M) = r)).card =
        ((Finset.powerset (Finset.range m)).filter
          (fun S =>
            ((S.sum (fun j => Nat.fib (j + 2)) : ℕ) : ZMod M) =
              (Sigma : ZMod M) - r)).card := by
  classical
  dsimp
  intro r
  let A : Finset ℕ := Finset.range m
  let w : ℕ → ℕ := fun j => Nat.fib (j + 2)
  change
    (A.powerset.filter
        (fun S => ((S.sum w : ℕ) : ZMod (Nat.fib (m + 2))) = r)).card =
      (A.powerset.filter
        (fun S =>
          ((S.sum w : ℕ) : ZMod (Nat.fib (m + 2))) =
            ((A.sum w : ℕ) : ZMod (Nat.fib (m + 2))) - r)).card
  refine Finset.card_bij (fun S _ => A \ S) ?_ ?_ ?_
  · intro S hS
    rcases Finset.mem_filter.mp hS with ⟨hSpow, hsumS⟩
    have hsub : S ⊆ A := Finset.mem_powerset.mp hSpow
    refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.sdiff_subset), ?_⟩
    rw [xi_time_part60ab2_stable_spectrum_selfreciprocal_center_sum_complement m S hsub,
      hsumS]
  · intro S₁ hS₁ S₂ hS₂ hcomp
    rcases Finset.mem_filter.mp hS₁ with ⟨hS₁pow, _⟩
    rcases Finset.mem_filter.mp hS₂ with ⟨hS₂pow, _⟩
    have hsub₁ : S₁ ⊆ A := Finset.mem_powerset.mp hS₁pow
    have hsub₂ : S₂ ⊆ A := Finset.mem_powerset.mp hS₂pow
    ext x
    by_cases hxA : x ∈ A
    · have hnot : x ∉ S₁ ↔ x ∉ S₂ := by
        simpa [hxA] using congrArg (fun T : Finset ℕ => x ∈ T) hcomp
      constructor
      · intro hx₁
        by_contra hx₂
        exact (hnot.mpr hx₂) hx₁
      · intro hx₂
        by_contra hx₁
        exact (hnot.mp hx₁) hx₂
    · constructor
      · intro hx₁
        exact False.elim (hxA (hsub₁ hx₁))
      · intro hx₂
        exact False.elim (hxA (hsub₂ hx₂))
  · intro T hT
    rcases Finset.mem_filter.mp hT with ⟨hTpow, hsumT⟩
    have hsubT : T ⊆ A := Finset.mem_powerset.mp hTpow
    refine ⟨A \ T, ?_, ?_⟩
    · refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.sdiff_subset), ?_⟩
      rw [xi_time_part60ab2_stable_spectrum_selfreciprocal_center_sum_complement m T hsubT,
        hsumT]
      abel
    · exact xi_time_part60ab2_stable_spectrum_selfreciprocal_center_complement_complement hsubT

end Omega.Zeta
