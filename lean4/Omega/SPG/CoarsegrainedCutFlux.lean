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

/-! ### R450 payback: main identity `cutFlux = volumeBias`. -/

/-- The "ω_i=false, ω∉S, flip∈S" layer is in bijection with the
    "ω_i=true, ω∈S, flip∉S" layer via flipAt. -/
theorem flipAt_bop_card_eq {n : ℕ} (i : Fin n)
    (S : Finset (Fin n → Bool)) :
    (Finset.univ.filter
      (fun ω : Fin n → Bool => ω i = false ∧ ω ∉ S ∧ flipAt i ω ∈ S)).card =
    (Finset.univ.filter
      (fun ω : Fin n → Bool => ω i = true ∧ ω ∈ S ∧ flipAt i ω ∉ S)).card := by
  refine Finset.card_bij (fun ω _ => flipAt i ω) ?_ ?_ ?_
  · intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
    obtain ⟨hω_i, hωS, hflipS⟩ := hω
    refine ⟨?_, hflipS, ?_⟩
    · unfold flipAt; simp [hω_i]
    · rw [flipAt_flipAt]; exact hωS
  · intro ω₁ _ ω₂ _ heq
    exact flipAt_injective i heq
  · intro ω' hω'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω'
    obtain ⟨hω'_i, hω'S, hflipS⟩ := hω'
    refine ⟨flipAt i ω', ?_, flipAt_flipAt i ω'⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨?_, ?_, ?_⟩
    · unfold flipAt; simp [hω'_i]
    · exact hflipS
    · rw [flipAt_flipAt]; exact hω'S

/-- Decomposition of the `ω_i = false` layer of S into A ∪ C (disjoint). -/
theorem s_false_layer_card_split {n : ℕ} (i : Fin n)
    (S : Finset (Fin n → Bool)) :
    (S.filter (fun ω => ω i = false)).card =
      (Finset.univ.filter
        (fun ω : Fin n → Bool => ω i = false ∧ ω ∈ S ∧ flipAt i ω ∉ S)).card +
      (Finset.univ.filter
        (fun ω : Fin n → Bool => ω i = false ∧ ω ∈ S ∧ flipAt i ω ∈ S)).card := by
  -- Both the LHS and the A+C split are expressible as filter cardinalities
  -- on Finset.univ with conjunction predicates; we rewrite via filter_filter
  -- then card_union_of_disjoint over the "flip ∉ S" / "flip ∈ S" dichotomy.
  rw [show (S.filter (fun ω => ω i = false)) =
        Finset.univ.filter (fun ω : Fin n → Bool => ω i = false ∧ ω ∈ S) from by
      ext ω; simp [Finset.mem_filter, and_comm]]
  rw [← Finset.card_filter_add_card_filter_not
        (s := Finset.univ.filter (fun ω : Fin n → Bool => ω i = false ∧ ω ∈ S))
        (p := fun ω => flipAt i ω ∉ S)]
  congr 1
  · congr 1
    ext ω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  · congr 1
    ext ω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not]
    tauto

/-- Decomposition of the `ω_i = true` layer of S into B' ∪ C' (disjoint). -/
theorem s_true_layer_card_split {n : ℕ} (i : Fin n)
    (S : Finset (Fin n → Bool)) :
    (S.filter (fun ω => ω i = true)).card =
      (Finset.univ.filter
        (fun ω : Fin n → Bool => ω i = true ∧ ω ∈ S ∧ flipAt i ω ∉ S)).card +
      (Finset.univ.filter
        (fun ω : Fin n → Bool => ω i = true ∧ ω ∈ S ∧ flipAt i ω ∈ S)).card := by
  rw [show (S.filter (fun ω => ω i = true)) =
        Finset.univ.filter (fun ω : Fin n → Bool => ω i = true ∧ ω ∈ S) from by
      ext ω; simp [Finset.mem_filter, and_comm]]
  rw [← Finset.card_filter_add_card_filter_not
        (s := Finset.univ.filter (fun ω : Fin n → Bool => ω i = true ∧ ω ∈ S))
        (p := fun ω => flipAt i ω ∉ S)]
  congr 1
  · congr 1
    ext ω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  · congr 1
    ext ω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not]
    tauto

/-- volumeBias rewritten as a signed cardinality difference of the two
    boolean layers of S. -/
theorem volumeBias_eq_layer_diff {n : ℕ} (i : Fin n)
    (S : Finset (Fin n → Bool)) :
    volumeBias i S =
      ((S.filter (fun ω => ω i = false)).card : ℤ)
      - ((S.filter (fun ω => ω i = true)).card : ℤ) := by
  unfold volumeBias
  rw [← Finset.sum_filter_add_sum_filter_not S (fun ω => ω i = false)]
  have h1 : ∀ ω ∈ S.filter (fun ω => ω i = false),
      (if ω i = false then (1 : ℤ) else -1) = 1 := by
    intro ω hω
    rw [Finset.mem_filter] at hω
    simp [hω.2]
  have h2 : ∀ ω ∈ S.filter (fun ω => ¬ (ω i = false)),
      (if ω i = false then (1 : ℤ) else -1) = -1 := by
    intro ω hω
    rw [Finset.mem_filter] at hω
    simp [hω.2]
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2]
  have hset : (S.filter (fun ω => ¬ (ω i = false))) =
              S.filter (fun ω => ω i = true) := by
    ext ω
    simp only [Finset.mem_filter, and_congr_right_iff]
    intro _
    cases ω i <;> simp
  rw [hset]
  simp
  ring

/-- Main identity: Φ_i(S) = b_i(S).
    thm:spg-coarsegrained-cut-flux-volume-bias -/
theorem cutFlux_eq_volumeBias {n : ℕ} (i : Fin n)
    (S : Finset (Fin n → Bool)) :
    cutFlux i S = volumeBias i S := by
  rw [volumeBias_eq_layer_diff]
  have h_false := s_false_layer_card_split i S
  have h_true := s_true_layer_card_split i S
  have h_bop_eq_b' := flipAt_bop_card_eq i S
  have h_c_eq_c' := flipAt_card_filter_eq i S
  unfold cutFlux
  zify at h_false h_true h_bop_eq_b' h_c_eq_c'
  linarith

/-- Paper-facing pullback form of the coarse-grained cut-flux identity: for a coarse graining
    `f : Ωₙ → X` and a subset `U ⊆ X`, the region `S = f⁻¹(U)` satisfies the same flux/bias
    identity as the underlying Boolean cube region.
    thm:spg-coarsegrained-cut-flux-volume-bias -/
theorem paper_spg_coarsegrained_cut_flux_volume_bias {n : ℕ} {X : Type*}
    [Fintype X] [DecidableEq X]
    (i : Fin n) (f : (Fin n → Bool) → X) (_hf : Function.Surjective f) (U : Finset X) :
    (((Finset.univ.filter
      (fun ω : Fin n → Bool => ω i = false ∧ f ω ∈ U ∧ f (flipAt i ω) ∉ U)).card : ℤ)
      - ((Finset.univ.filter
        (fun ω : Fin n → Bool => ω i = false ∧ f ω ∉ U ∧ f (flipAt i ω) ∈ U)).card : ℤ)) =
      ∑ ω ∈ Finset.univ.filter (fun ω : Fin n → Bool => f ω ∈ U),
        (if ω i = false then (1 : ℤ) else -1) := by
  simpa [cutFlux, volumeBias] using
    cutFlux_eq_volumeBias i (Finset.univ.filter (fun ω : Fin n → Bool => f ω ∈ U))

end Omega.SPG
