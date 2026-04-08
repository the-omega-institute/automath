import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

namespace Omega.SPG

/-- Flip the `i`-th coordinate of a boolean configuration.
    thm:spg-coarsegrained-cut-flux-volume-bias -/
def flipAt {n : ℕ} (i : Fin n) (ω : Fin n → Bool) : Fin n → Bool :=
  Function.update ω i (!ω i)

/-- Signed cut flux through direction `i` for a region `S`.
    thm:spg-coarsegrained-cut-flux-volume-bias -/
noncomputable def cutFlux {n : ℕ} (i : Fin n)
    (S : Finset (Fin n → Bool)) : ℤ :=
  ((Finset.univ.filter
    (fun ω => ω i = false ∧ ω ∈ S ∧ flipAt i ω ∉ S)).card : ℤ)
  - ((Finset.univ.filter
    (fun ω => ω i = false ∧ ω ∉ S ∧ flipAt i ω ∈ S)).card : ℤ)

/-- Volume bias along direction `i` for a region `S`.
    thm:spg-coarsegrained-cut-flux-volume-bias -/
noncomputable def volumeBias {n : ℕ} (i : Fin n)
    (S : Finset (Fin n → Bool)) : ℤ :=
  ∑ ω ∈ S, (if ω i = false then (1 : ℤ) else -1)

/-- flipAt is an involution.
    thm:spg-coarsegrained-cut-flux-volume-bias -/
theorem flipAt_flipAt {n : ℕ} (i : Fin n) (ω : Fin n → Bool) :
    flipAt i (flipAt i ω) = ω := by
  funext j
  unfold flipAt
  by_cases hj : j = i
  · subst hj; simp [Function.update]
  · simp [Function.update, hj]

/-- cutFlux is zero on the empty region.
    thm:spg-coarsegrained-cut-flux-volume-bias -/
theorem cutFlux_empty {n : ℕ} (i : Fin n) :
    cutFlux i (∅ : Finset (Fin n → Bool)) = 0 := by
  unfold cutFlux
  simp

/-- volumeBias is zero on the empty region.
    thm:spg-coarsegrained-cut-flux-volume-bias -/
theorem volumeBias_empty {n : ℕ} (i : Fin n) :
    volumeBias i (∅ : Finset (Fin n → Bool)) = 0 := by
  unfold volumeBias
  simp

/-- Paper-facing skeleton package: definitions, involution, empty cases, and
    coordinate-level flipAt properties. Main identity Φ = b deferred.
    thm:spg-coarsegrained-cut-flux-volume-bias -/
theorem paper_spg_cut_flux_volume_bias_skeleton :
    (∀ (n : ℕ) (i : Fin n), cutFlux i (∅ : Finset (Fin n → Bool)) = 0) ∧
    (∀ (n : ℕ) (i : Fin n), volumeBias i (∅ : Finset (Fin n → Bool)) = 0) ∧
    (∀ (n : ℕ) (i : Fin n) (ω : Fin n → Bool),
      flipAt i (flipAt i ω) = ω) ∧
    (∀ (n : ℕ) (i : Fin n) (ω : Fin n → Bool),
      flipAt i ω i = !ω i) ∧
    (∀ (n : ℕ) (i : Fin n) (ω : Fin n → Bool) (j : Fin n),
      j ≠ i → flipAt i ω j = ω j) := by
  refine ⟨@cutFlux_empty, @volumeBias_empty, @flipAt_flipAt, ?_, ?_⟩
  · intro n i ω
    unfold flipAt
    simp [Function.update]
  · intro n i ω j hj
    unfold flipAt
    simp [Function.update, hj]

end Omega.SPG
