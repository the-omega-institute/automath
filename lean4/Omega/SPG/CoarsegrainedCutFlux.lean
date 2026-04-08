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

/-! ### R449 payback: flipAt bijection lemmas towards `cutFlux = volumeBias`.

    The full main identity `Φ_i(S) = b_i(S)` is delivered in R450 after this
    bijection infrastructure. Here we register the two cardinality bijections
    induced by `flipAt`, which are the combinatorial heart of the argument. -/

/-- flipAt is injective (it is its own inverse).
    thm:spg-coarsegrained-cut-flux-volume-bias -/
theorem flipAt_injective {n : ℕ} (i : Fin n) :
    Function.Injective (flipAt (n := n) i) := by
  intro ω₁ ω₂ h
  have := congrArg (flipAt i) h
  rwa [flipAt_flipAt, flipAt_flipAt] at this

/-- flipAt sends the `ω_i = false` layer bijectively onto the `ω_i = true` layer,
    as a cardinality equality on arbitrary sub-filters respected by flipAt.
    thm:spg-coarsegrained-cut-flux-volume-bias -/
theorem flipAt_card_filter_eq {n : ℕ} (i : Fin n)
    (S : Finset (Fin n → Bool)) :
    (Finset.univ.filter
      (fun ω : Fin n → Bool => ω i = false ∧ ω ∈ S ∧ flipAt i ω ∈ S)).card =
    (Finset.univ.filter
      (fun ω : Fin n → Bool => ω i = true ∧ ω ∈ S ∧ flipAt i ω ∈ S)).card := by
  refine Finset.card_bij (fun ω _ => flipAt i ω) ?_ ?_ ?_
  · intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
    obtain ⟨hω_i, hωS, hflipS⟩ := hω
    refine ⟨?_, hflipS, ?_⟩
    · unfold flipAt; simp [hω_i]
    · rw [flipAt_flipAt]; exact hωS
  · intro ω₁ h₁ ω₂ h₂ heq
    exact flipAt_injective i heq
  · intro ω' hω'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω'
    obtain ⟨hω'_i, hω'S, hflipS⟩ := hω'
    refine ⟨flipAt i ω', ?_, flipAt_flipAt i ω'⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨?_, hflipS, ?_⟩
    · unfold flipAt; simp [hω'_i]
    · rw [flipAt_flipAt]; exact hω'S

/-- Paper-facing bijection lemma (R449 payback partial): the number of
    `ω_i = false` elements of `S` whose flip also lies in `S` equals the
    number of `ω_i = true` elements of `S` whose flip also lies in `S`.
    thm:spg-coarsegrained-cut-flux-volume-bias -/
theorem paper_cut_flux_flip_pairing_card {n : ℕ} (i : Fin n)
    (S : Finset (Fin n → Bool)) :
    (Finset.univ.filter
      (fun ω : Fin n → Bool => ω i = false ∧ ω ∈ S ∧ flipAt i ω ∈ S)).card =
    (Finset.univ.filter
      (fun ω : Fin n → Bool => ω i = true ∧ ω ∈ S ∧ flipAt i ω ∈ S)).card :=
  flipAt_card_filter_eq i S

end Omega.SPG
