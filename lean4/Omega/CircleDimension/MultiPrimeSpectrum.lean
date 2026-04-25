import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace Omega.CircleDimension

abbrev PrimeSupport := Finset Nat

def multiPrimeSpectrum (supports : Finset PrimeSupport) (J : PrimeSupport) : Nat :=
  (supports.filter fun S => J ⊆ S).card

/-- Type count n_A(J): exact-support multiplicity.
    thm:cdim-mobius-inversion-localization-multiset-classification -/
def typeCount (supports : Finset PrimeSupport) (J : PrimeSupport) : Nat :=
  (supports.filter fun S => S = J).card

/-- Induced spectrum from finitely many support types with multiplicity function `n`.
    thm:cdim-multiprime-spectrum-realizability -/
def inducedSpectrum (supports : Finset PrimeSupport) (n : PrimeSupport → Nat) (J : PrimeSupport) : Nat :=
  Finset.sum supports (fun K => if J ⊆ K then n K else 0)

/-- Explicit count formula for the divisible multiprime spectrum.
    prop:cdim-multiprime-divisible-spectrum-explicit -/
theorem multiPrimeSpectrum_eq_count (supports : Finset PrimeSupport) (J : PrimeSupport) :
    multiPrimeSpectrum supports J = (supports.filter fun S => J ⊆ S).card := rfl

/-- Antitone in the prime support parameter.
    prop:cdim-multiprime-divisible-spectrum-explicit -/
theorem multiPrimeSpectrum_anti_mono {supports : Finset PrimeSupport} {J K : PrimeSupport}
    (hJK : J ⊆ K) :
    multiPrimeSpectrum supports K ≤ multiPrimeSpectrum supports J := by
  unfold multiPrimeSpectrum
  apply Finset.card_le_card
  intro S hS
  simp only [Finset.mem_filter] at hS ⊢
  exact ⟨hS.1, fun x hxJ => hS.2 (hJK hxJ)⟩

/-- Empty support is counted by every support set.
    prop:cdim-multiprime-divisible-spectrum-explicit -/
theorem multiPrimeSpectrum_empty (supports : Finset PrimeSupport) :
    multiPrimeSpectrum supports ∅ = supports.card := by
  unfold multiPrimeSpectrum
  simp

/-- Any support counts itself, hence contributes positive spectrum mass.
    prop:cdim-multiprime-divisible-spectrum-explicit -/
theorem multiPrimeSpectrum_pos_of_mem {supports : Finset PrimeSupport} {J : PrimeSupport}
    (hJ : J ∈ supports) :
    0 < multiPrimeSpectrum supports J := by
  unfold multiPrimeSpectrum
  apply Finset.card_pos.mpr
  refine ⟨J, ?_⟩
  simp [hJ]

/-- Multiprime spectrum is additive under disjoint union of support lists.
    prop:cdim-multiprime-divisible-spectrum-explicit -/
theorem multiPrimeSpectrum_disjoint_add
    (s₁ s₂ : Finset PrimeSupport) (hd : Disjoint s₁ s₂) (J : PrimeSupport) :
    multiPrimeSpectrum (s₁ ∪ s₂) J = multiPrimeSpectrum s₁ J + multiPrimeSpectrum s₂ J := by
  unfold multiPrimeSpectrum
  rw [Finset.filter_union]
  exact Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hd)

/-- Zeta-transform identity: the spectrum is the finite sum of exact-support counts.
    thm:cdim-mobius-inversion-localization-multiset-classification -/
theorem multiPrimeSpectrum_eq_sum_typeCount
    (supports : Finset PrimeSupport) (J : PrimeSupport) :
    multiPrimeSpectrum supports J =
      Finset.sum supports (fun K => if J ⊆ K then typeCount supports K else 0) := by
  have htc : ∀ {K : PrimeSupport}, K ∈ supports → typeCount supports K = 1 := by
    intro K hK
    unfold typeCount
    have hEq : supports.filter (fun S => S = K) = {K} := by
      ext x
      constructor
      · intro hx
        simp only [Finset.mem_filter, Finset.mem_singleton] at hx ⊢
        exact hx.2
      · intro hx
        simp only [Finset.mem_filter, Finset.mem_singleton] at hx ⊢
        subst hx
        exact ⟨hK, rfl⟩
    rw [hEq]
    simp
  unfold multiPrimeSpectrum
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  refine Finset.sum_congr rfl ?_
  intro K hK
  by_cases hJK : J ⊆ K
  · simp [hJK, htc hK]
  · simp [hJK]

/-- Total type count equals the total number of supports.
    thm:cdim-mobius-inversion-localization-multiset-classification -/
theorem sum_typeCount_eq_card (supports : Finset PrimeSupport) :
    Finset.sum supports (typeCount supports) = supports.card := by
  have htc : ∀ {K : PrimeSupport}, K ∈ supports → typeCount supports K = 1 := by
    intro K hK
    unfold typeCount
    have hEq : supports.filter (fun S => S = K) = {K} := by
      ext x
      constructor
      · intro hx
        simp only [Finset.mem_filter, Finset.mem_singleton] at hx ⊢
        exact hx.2
      · intro hx
        simp only [Finset.mem_filter, Finset.mem_singleton] at hx ⊢
        subst hx
        exact ⟨hK, rfl⟩
    rw [hEq]
    simp
  rw [Finset.card_eq_sum_ones]
  refine Finset.sum_congr rfl ?_
  intro K hK
  simp [htc hK]

/-- A singleton type count is bounded by any spectrum indexed by a subset.
    thm:cdim-mobius-inversion-localization-multiset-classification -/
theorem typeCount_le_multiPrimeSpectrum_of_subset
    {supports : Finset PrimeSupport} {J K : PrimeSupport}
    (hJK : J ⊆ K) :
    typeCount supports K ≤ multiPrimeSpectrum supports J := by
  unfold typeCount multiPrimeSpectrum
  apply Finset.card_le_card
  intro S hS
  simp only [Finset.mem_filter] at hS ⊢
  constructor
  · exact hS.1
  · simpa [hS.2] using hJK

/-- Every type count is bounded by the empty-support spectrum.
    thm:cdim-mobius-inversion-localization-multiset-classification -/
theorem typeCount_le_multiPrimeSpectrum_empty
    (supports : Finset PrimeSupport) (K : PrimeSupport) :
    typeCount supports K ≤ multiPrimeSpectrum supports ∅ := by
  exact typeCount_le_multiPrimeSpectrum_of_subset (J := ∅) (K := K) (by simp)

/-- Singleton-support realizability shadow.
    thm:cdim-multiprime-spectrum-realizability -/
theorem inducedSpectrum_singleton
    (K J : PrimeSupport) (n : Nat) :
    inducedSpectrum ({K} : Finset PrimeSupport) (fun S => if S = K then n else 0) J
      = if J ⊆ K then n else 0 := by
  unfold inducedSpectrum
  by_cases hJK : J ⊆ K
  · simp [hJK]
  · simp [hJK]

/-- Empty-support specialization of the singleton-shadow formula.
    thm:cdim-multiprime-spectrum-realizability -/
theorem inducedSpectrum_singleton_empty (K : PrimeSupport) (n : Nat) :
    inducedSpectrum ({K} : Finset PrimeSupport) (fun S => if S = K then n else 0) ∅ = n := by
  simpa using inducedSpectrum_singleton K ∅ n

/-- One-prime marginals do not determine the higher support spectrum.
    prop:cdim-higher-spectrum-not-determined-by-marginals -/
theorem higher_spectrum_not_determined_by_marginals
    {p q : Nat} (hpq : p ≠ q) :
    let A : Finset PrimeSupport := {({p} : PrimeSupport), {q}}
    let A' : Finset PrimeSupport := {({p, q} : PrimeSupport), (∅ : PrimeSupport)}
    (∀ ℓ : Nat,
        multiPrimeSpectrum A ({ℓ} : PrimeSupport) =
          multiPrimeSpectrum A' ({ℓ} : PrimeSupport)) ∧
      multiPrimeSpectrum A ({p, q} : PrimeSupport) ≠
        multiPrimeSpectrum A' ({p, q} : PrimeSupport) := by
  constructor
  · intro ℓ
    by_cases hℓp : ℓ = p
    · unfold multiPrimeSpectrum
      have hLeft :
          {S ∈ ({({p} : PrimeSupport), ({q} : PrimeSupport)} : Finset PrimeSupport) |
              ({ℓ} : PrimeSupport) ⊆ S} = {({p} : PrimeSupport)} := by
        ext S
        constructor
        · intro h
          rw [hℓp] at h
          simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton,
            Finset.singleton_subset_iff] at h
          rcases h with ⟨hS, hpS⟩
          rcases hS with rfl | rfl
          · simp
          · have : p = q := by simpa using hpS
            exact (hpq this).elim
        · intro h
          simp only [Finset.mem_singleton] at h
          subst h
          rw [hℓp]
          simp
      have hRight :
          {S ∈ ({({p, q} : PrimeSupport), (∅ : PrimeSupport)} : Finset PrimeSupport) |
              ({ℓ} : PrimeSupport) ⊆ S} = {({p, q} : PrimeSupport)} := by
        ext S
        constructor
        · intro h
          rw [hℓp] at h
          simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton,
            Finset.singleton_subset_iff] at h
          rcases h with ⟨hS, hpS⟩
          rcases hS with rfl | rfl
          · simp
          · simp at hpS
        · intro h
          simp only [Finset.mem_singleton] at h
          subst h
          rw [hℓp]
          simp
      rw [hLeft, hRight]
      simp
    · by_cases hℓq : ℓ = q
      · unfold multiPrimeSpectrum
        have hLeft :
            {S ∈ ({({p} : PrimeSupport), ({q} : PrimeSupport)} : Finset PrimeSupport) |
                ({ℓ} : PrimeSupport) ⊆ S} = {({q} : PrimeSupport)} := by
          ext S
          constructor
          · intro h
            rw [hℓq] at h
            simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton,
              Finset.singleton_subset_iff] at h
            rcases h with ⟨hS, hqS⟩
            rcases hS with rfl | rfl
            · have : q = p := by simpa using hqS
              exact (hpq this.symm).elim
            · simp
          · intro h
            simp only [Finset.mem_singleton] at h
            subst h
            rw [hℓq]
            simp
        have hRight :
            {S ∈ ({({p, q} : PrimeSupport), (∅ : PrimeSupport)} : Finset PrimeSupport) |
                ({ℓ} : PrimeSupport) ⊆ S} = {({p, q} : PrimeSupport)} := by
          ext S
          constructor
          · intro h
            rw [hℓq] at h
            simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton,
              Finset.singleton_subset_iff] at h
            rcases h with ⟨hS, hqS⟩
            rcases hS with rfl | rfl
            · simp
            · simp at hqS
          · intro h
            simp only [Finset.mem_singleton] at h
            subst h
            rw [hℓq]
            simp
        rw [hLeft, hRight]
        simp
      · unfold multiPrimeSpectrum
        have hLeft :
            {S ∈ ({({p} : PrimeSupport), ({q} : PrimeSupport)} : Finset PrimeSupport) |
                ({ℓ} : PrimeSupport) ⊆ S} = ∅ := by
          ext S
          constructor
          · intro h
            simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton,
              Finset.singleton_subset_iff] at h
            rcases h with ⟨hS, hℓS⟩
            rcases hS with rfl | rfl
            · exact (hℓp <| by simpa using hℓS).elim
            · exact (hℓq <| by simpa using hℓS).elim
          · intro h
            simp at h
        have hRight :
            {S ∈ ({({p, q} : PrimeSupport), (∅ : PrimeSupport)} : Finset PrimeSupport) |
                ({ℓ} : PrimeSupport) ⊆ S} = ∅ := by
          ext S
          constructor
          · intro h
            simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton,
              Finset.singleton_subset_iff] at h
            rcases h with ⟨hS, hℓS⟩
            rcases hS with rfl | rfl
            · have hpEq : ℓ = p ∨ ℓ = q := by
                simpa [Finset.mem_insert, Finset.mem_singleton] using hℓS
              cases hpEq with
              | inl hpEq => exact (hℓp hpEq).elim
              | inr hqEq => exact (hℓq hqEq).elim
            · simp at hℓS
          · intro h
            simp at h
        rw [hLeft, hRight]
  · unfold multiPrimeSpectrum
    have hLeft :
        {S ∈ ({({p} : PrimeSupport), ({q} : PrimeSupport)} : Finset PrimeSupport) |
            ({p, q} : PrimeSupport) ⊆ S} = ∅ := by
      ext S
      constructor
      · intro h
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] at h
        rcases h with ⟨hS, hsub⟩
        rcases hS with rfl | rfl
        · have hqS : q ∈ ({p} : PrimeSupport) := hsub (by simp)
          have : q = p := by simpa using hqS
          exact (hpq this.symm).elim
        · have hpS : p ∈ ({q} : PrimeSupport) := hsub (by simp)
          have : p = q := by simpa using hpS
          exact (hpq this).elim
      · intro h
        simp at h
    have hRight :
        {S ∈ ({({p, q} : PrimeSupport), (∅ : PrimeSupport)} : Finset PrimeSupport) |
            ({p, q} : PrimeSupport) ⊆ S} = {({p, q} : PrimeSupport)} := by
      ext S
      constructor
      · intro h
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] at h
        rcases h with ⟨hS, hsub⟩
        rcases hS with rfl | rfl
        · simp
        · simp at hsub
      · intro h
        simp only [Finset.mem_singleton] at h
        subst h
        simp
    rw [hLeft, hRight]
    simp

/-- Singleton marginals for the higher-spectrum counterexample have the shared `if` formula.
    prop:cdim-higher-spectrum-not-determined-by-marginals -/
theorem higher_spectrum_counterexample_singleton_formula
    {p q ℓ : Nat} (hpq : p ≠ q) :
    let A : Finset PrimeSupport := {({p} : PrimeSupport), {q}}
    let A' : Finset PrimeSupport := {({p, q} : PrimeSupport), (∅ : PrimeSupport)}
    (multiPrimeSpectrum A ({ℓ} : PrimeSupport) =
        if ℓ = p ∨ ℓ = q then 1 else 0) ∧
      (multiPrimeSpectrum A' ({ℓ} : PrimeSupport) =
        if ℓ = p ∨ ℓ = q then 1 else 0) := by
  by_cases hℓp : ℓ = p
  · have hℓq : ℓ ≠ q := by
      intro h
      apply hpq
      calc
        p = ℓ := hℓp.symm
        _ = q := h
    unfold multiPrimeSpectrum
    have hLeft :
        {S ∈ ({({p} : PrimeSupport), ({q} : PrimeSupport)} : Finset PrimeSupport) |
            ({ℓ} : PrimeSupport) ⊆ S} = {({p} : PrimeSupport)} := by
      ext S
      constructor
      · intro h
        rw [hℓp] at h
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton,
          Finset.singleton_subset_iff] at h
        rcases h with ⟨hS, hpS⟩
        rcases hS with rfl | rfl
        · simp
        · have : p = q := by simpa using hpS
          exact (hpq this).elim
      · intro h
        simp only [Finset.mem_singleton] at h
        subst h
        rw [hℓp]
        simp
    have hRight :
        {S ∈ ({({p, q} : PrimeSupport), (∅ : PrimeSupport)} : Finset PrimeSupport) |
            ({ℓ} : PrimeSupport) ⊆ S} = {({p, q} : PrimeSupport)} := by
      ext S
      constructor
      · intro h
        rw [hℓp] at h
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton,
          Finset.singleton_subset_iff] at h
        rcases h with ⟨hS, hpS⟩
        rcases hS with rfl | rfl
        · simp
        · simp at hpS
      · intro h
        simp only [Finset.mem_singleton] at h
        subst h
        rw [hℓp]
        simp
    constructor
    · rw [hLeft]
      simp [hℓp]
    · rw [hRight]
      simp [hℓp]
  · by_cases hℓq : ℓ = q
    · unfold multiPrimeSpectrum
      have hLeft :
          {S ∈ ({({p} : PrimeSupport), ({q} : PrimeSupport)} : Finset PrimeSupport) |
              ({ℓ} : PrimeSupport) ⊆ S} = {({q} : PrimeSupport)} := by
        ext S
        constructor
        · intro h
          rw [hℓq] at h
          simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton,
            Finset.singleton_subset_iff] at h
          rcases h with ⟨hS, hqS⟩
          rcases hS with rfl | rfl
          · have : q = p := by simpa using hqS
            exact (hpq this.symm).elim
          · simp
        · intro h
          simp only [Finset.mem_singleton] at h
          subst h
          rw [hℓq]
          simp
      have hRight :
          {S ∈ ({({p, q} : PrimeSupport), (∅ : PrimeSupport)} : Finset PrimeSupport) |
              ({ℓ} : PrimeSupport) ⊆ S} = {({p, q} : PrimeSupport)} := by
        ext S
        constructor
        · intro h
          rw [hℓq] at h
          simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton,
            Finset.singleton_subset_iff] at h
          rcases h with ⟨hS, hqS⟩
          rcases hS with rfl | rfl
          · simp
          · simp at hqS
        · intro h
          simp only [Finset.mem_singleton] at h
          subst h
          rw [hℓq]
          simp
      constructor
      · rw [hLeft]
        simp [hℓq]
      · rw [hRight]
        simp [hℓq]
    · unfold multiPrimeSpectrum
      have hLeft :
          {S ∈ ({({p} : PrimeSupport), ({q} : PrimeSupport)} : Finset PrimeSupport) |
              ({ℓ} : PrimeSupport) ⊆ S} = ∅ := by
        ext S
        constructor
        · intro h
          simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton,
            Finset.singleton_subset_iff] at h
          rcases h with ⟨hS, hℓS⟩
          rcases hS with rfl | rfl
          · exact (hℓp <| by simpa using hℓS).elim
          · exact (hℓq <| by simpa using hℓS).elim
        · intro h
          simp at h
      have hRight :
          {S ∈ ({({p, q} : PrimeSupport), (∅ : PrimeSupport)} : Finset PrimeSupport) |
              ({ℓ} : PrimeSupport) ⊆ S} = ∅ := by
        ext S
        constructor
        · intro h
          simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton,
            Finset.singleton_subset_iff] at h
          rcases h with ⟨hS, hℓS⟩
          rcases hS with rfl | rfl
          · have hpEq : ℓ = p ∨ ℓ = q := by
              simpa [Finset.mem_insert, Finset.mem_singleton] using hℓS
            cases hpEq with
            | inl hpEq => exact (hℓp hpEq).elim
            | inr hqEq => exact (hℓq hqEq).elim
          · simp at hℓS
        · intro h
          simp at h
      constructor
      · rw [hLeft]
        simp [hℓp, hℓq]
      · rw [hRight]
        simp [hℓp, hℓq]

/-- The pair support separates the higher-spectrum counterexample.
    prop:cdim-higher-spectrum-not-determined-by-marginals -/
theorem higher_spectrum_counterexample_pair_values
    {p q : Nat} (hpq : p ≠ q) :
    let A : Finset PrimeSupport := {({p} : PrimeSupport), {q}}
    let A' : Finset PrimeSupport := {({p, q} : PrimeSupport), (∅ : PrimeSupport)}
    (multiPrimeSpectrum A ({p, q} : PrimeSupport) = 0) ∧
      (multiPrimeSpectrum A' ({p, q} : PrimeSupport) = 1) := by
  unfold multiPrimeSpectrum
  constructor
  · have hLeft :
        {S ∈ ({({p} : PrimeSupport), ({q} : PrimeSupport)} : Finset PrimeSupport) |
            ({p, q} : PrimeSupport) ⊆ S} = ∅ := by
      ext S
      constructor
      · intro h
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] at h
        rcases h with ⟨hS, hsub⟩
        rcases hS with rfl | rfl
        · have hqS : q ∈ ({p} : PrimeSupport) := hsub (by simp)
          have : q = p := by simpa using hqS
          exact (hpq this.symm).elim
        · have hpS : p ∈ ({q} : PrimeSupport) := hsub (by simp)
          have : p = q := by simpa using hpS
          exact (hpq this).elim
      · intro h
        simp at h
    rw [hLeft]
    simp
  · have hRight :
        {S ∈ ({({p, q} : PrimeSupport), (∅ : PrimeSupport)} : Finset PrimeSupport) |
            ({p, q} : PrimeSupport) ⊆ S} = {({p, q} : PrimeSupport)} := by
      ext S
      constructor
      · intro h
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] at h
        rcases h with ⟨hS, hsub⟩
        rcases hS with rfl | rfl
        · simp
        · simp at hsub
      · intro h
        simp only [Finset.mem_singleton] at h
        subst h
        simp
    rw [hRight]
    simp

/-- The repaired higher-spectrum formula for the counterexample support `A'`.
    prop:cdim-higher-spectrum-not-determined-by-marginals -/
theorem higher_spectrum_counterexample_Aprime_piecewise
    {p q : Nat} (hpq : p ≠ q) (J : PrimeSupport) :
    let A' : Finset PrimeSupport := {({p, q} : PrimeSupport), (∅ : PrimeSupport)}
    multiPrimeSpectrum A' J =
      if J = ∅ then 2 else if J ⊆ ({p, q} : PrimeSupport) then 1 else 0 := by
  let _ := hpq
  by_cases hJ0 : J = ∅
  · subst hJ0
    simp [multiPrimeSpectrum_empty]
  · by_cases hJ : J ⊆ ({p, q} : PrimeSupport)
    · have hFilter :
          {S ∈ ({({p, q} : PrimeSupport), (∅ : PrimeSupport)} : Finset PrimeSupport) | J ⊆ S} =
            {({p, q} : PrimeSupport)} := by
        ext S
        constructor
        · intro h
          simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] at h
          rcases h with ⟨hS, hsub⟩
          rcases hS with rfl | rfl
          · simp
          · exfalso
            apply hJ0
            ext x
            constructor
            · intro hx
              exfalso
              simpa using hsub hx
            · intro hx
              simp at hx
        · intro h
          simp only [Finset.mem_singleton] at h
          subst h
          simp [hJ]
      simp [multiPrimeSpectrum, hFilter, hJ0, hJ]
    · have hFilter :
          {S ∈ ({({p, q} : PrimeSupport), (∅ : PrimeSupport)} : Finset PrimeSupport) | J ⊆ S} = ∅ := by
        ext S
        constructor
        · intro h
          simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] at h
          rcases h with ⟨hS, hsub⟩
          rcases hS with rfl | rfl
          · exact (hJ hsub).elim
          · exfalso
            apply hJ0
            ext x
            constructor
            · intro hx
              exfalso
              simpa using hsub hx
            · intro hx
              simp at hx
        · intro h
          simp at h
      simp [multiPrimeSpectrum, hFilter, hJ0, hJ]

-- ══════════════════════════════════════════════════════════════
-- Phase R254: Spectrum singleton, pair, witness
-- ══════════════════════════════════════════════════════════════

/-- Spectrum of singleton: 1 if J ⊆ S, else 0.
    prop:cdim-multiprime-divisible-spectrum-explicit -/
theorem multiPrimeSpectrum_singleton (S : PrimeSupport) (J : PrimeSupport) :
    multiPrimeSpectrum {S} J = if J ⊆ S then 1 else 0 := by
  simp only [multiPrimeSpectrum, Finset.filter_singleton]
  split <;> simp_all

/-- Spectrum of pair {S₁, S₂} with S₁ ≠ S₂.
    prop:cdim-multiprime-divisible-spectrum-explicit -/
theorem multiPrimeSpectrum_pair (S₁ S₂ : PrimeSupport) (hne : S₁ ≠ S₂) (J : PrimeSupport) :
    multiPrimeSpectrum {S₁, S₂} J =
      (if J ⊆ S₁ then 1 else 0) + (if J ⊆ S₂ then 1 else 0) := by
  have hd : Disjoint ({S₁} : Finset PrimeSupport) {S₂} :=
    Finset.disjoint_singleton.mpr hne
  rw [show ({S₁, S₂} : Finset PrimeSupport) = {S₁} ∪ {S₂} from by simp]
  rw [multiPrimeSpectrum_disjoint_add _ _ hd]
  rw [multiPrimeSpectrum_singleton, multiPrimeSpectrum_singleton]

/-- Positive spectrum implies containment witness.
    prop:cdim-multiprime-divisible-spectrum-explicit -/
theorem multiPrimeSpectrum_support_witness
    (supports : Finset PrimeSupport) (J : PrimeSupport)
    (hpos : 0 < multiPrimeSpectrum supports J) :
    ∃ S ∈ supports, J ⊆ S := by
  rw [multiPrimeSpectrum] at hpos
  obtain ⟨S, hS⟩ := Finset.card_pos.mp hpos
  simp only [Finset.mem_filter] at hS
  exact ⟨S, hS.1, hS.2⟩

/-- Multi-prime spectrum Mobius inversion package.
    thm:cdim-mobius-inversion-localization-multiset-classification -/
theorem paper_multiPrimeSpectrum_mobius_package :
    (∀ (supports : Finset PrimeSupport) (J K : PrimeSupport),
      J ⊆ K → multiPrimeSpectrum supports K ≤ multiPrimeSpectrum supports J) ∧
    (∀ supports : Finset PrimeSupport,
      multiPrimeSpectrum supports ∅ = supports.card) ∧
    (∀ (s₁ s₂ : Finset PrimeSupport) (J : PrimeSupport),
      Disjoint s₁ s₂ →
      multiPrimeSpectrum (s₁ ∪ s₂) J = multiPrimeSpectrum s₁ J + multiPrimeSpectrum s₂ J) :=
  ⟨fun _ _ _ hJK => multiPrimeSpectrum_anti_mono hJK,
   multiPrimeSpectrum_empty,
   fun s₁ s₂ J hd => multiPrimeSpectrum_disjoint_add s₁ s₂ hd J⟩

/-- Induced spectrum base cases.
    thm:cdim-mobius-inversion-localization-multiset-classification -/
theorem paper_inducedSpectrum_base_cases :
    (∀ (K J : PrimeSupport) (n : Nat),
      inducedSpectrum ({K} : Finset PrimeSupport) (fun S => if S = K then n else 0) J
        = if J ⊆ K then n else 0) ∧
    (∀ (K : PrimeSupport) (n : Nat),
      inducedSpectrum ({K} : Finset PrimeSupport) (fun S => if S = K then n else 0) ∅ = n) ∧
    (∀ supports : Finset PrimeSupport,
      multiPrimeSpectrum supports ∅ = supports.card) :=
  ⟨inducedSpectrum_singleton, inducedSpectrum_singleton_empty, multiPrimeSpectrum_empty⟩

-- ══════════════════════════════════════════════════════════════
-- Phase R324: inducedSpectrum antitone
-- ══════════════════════════════════════════════════════════════

/-- Induced spectrum is antitone in the prime support parameter:
    larger support J ⊆ K means fewer matching supports.
    thm:cdim-multiprime-spectrum-realizability -/
theorem inducedSpectrum_antitone (supports : Finset PrimeSupport) (n : PrimeSupport → Nat)
    {J K : PrimeSupport} (hJK : J ⊆ K) :
    inducedSpectrum supports n K ≤ inducedSpectrum supports n J := by
  unfold inducedSpectrum
  apply Finset.sum_le_sum
  intro S _hS
  split_ifs with hK hJ
  · exact le_refl _
  · exact absurd (Finset.Subset.trans hJK hK) hJ
  · exact Nat.zero_le _
  · exact le_refl _

/-- Multi-prime spectrum is bounded by total support count.
    defprop:cdim-multiprime-divisible-spectrum -/
theorem multiPrimeSpectrum_le_card (supports : Finset PrimeSupport) (J : PrimeSupport) :
    multiPrimeSpectrum supports J ≤ supports.card := by
  calc multiPrimeSpectrum supports J
      ≤ multiPrimeSpectrum supports ∅ := multiPrimeSpectrum_anti_mono (Finset.empty_subset _)
    _ = supports.card := multiPrimeSpectrum_empty supports

-- Phase R601: Möbius inversion seeds
-- ══════════════════════════════════════════════════════════════

/-- Type count for any J is at most 1 (Finset elements are distinct).
    thm:cdim-mobius-inversion-localization-multiset-classification -/
theorem typeCount_le_one (supports : Finset PrimeSupport) (J : PrimeSupport) :
    typeCount supports J ≤ 1 := by
  unfold typeCount
  rw [Finset.card_le_one]
  intro a ha b hb
  simp only [Finset.mem_filter] at ha hb
  rw [ha.2, hb.2]

/-- Type count is bounded by multi-prime spectrum for any support J.
    thm:cdim-mobius-inversion-localization-multiset-classification -/
theorem typeCount_le_multiPrimeSpectrum (supports : Finset PrimeSupport) (J : PrimeSupport) :
    typeCount supports J ≤ multiPrimeSpectrum supports J := by
  exact typeCount_le_multiPrimeSpectrum_of_subset (Finset.Subset.refl J)

/-- Singleton spectrum bound: typeCount + multiPrimeSpectrum ≤ card + 1.
    thm:cdim-mobius-inversion-localization-multiset-classification -/
theorem typeCount_from_spectrum_singleton {supports : Finset PrimeSupport} {p : ℕ}
    (_hp : {p} ∈ supports) :
    typeCount supports {p} + multiPrimeSpectrum supports {p} ≤ supports.card + 1 := by
  calc typeCount supports {p} + multiPrimeSpectrum supports {p}
      ≤ 1 + supports.card :=
        Nat.add_le_add (typeCount_le_one supports {p}) (multiPrimeSpectrum_le_card supports {p})
    _ = supports.card + 1 := by omega

/-- Paper seeds: Möbius inversion at small support sets.
    thm:cdim-mobius-inversion-localization-multiset-classification -/
theorem paper_cdim_mobius_inversion_seeds :
    (let S : Finset PrimeSupport := {{2}}
     multiPrimeSpectrum S ∅ = 1 ∧ multiPrimeSpectrum S {2} = 1 ∧ typeCount S {2} = 1) ∧
    (let S : Finset PrimeSupport := {{2}, {3}}
     multiPrimeSpectrum S ∅ = 2 ∧ multiPrimeSpectrum S {2} = 1 ∧
     multiPrimeSpectrum S {3} = 1 ∧ multiPrimeSpectrum S {2, 3} = 0) := by
  constructor
  · constructor
    · native_decide
    constructor
    · native_decide
    · native_decide
  · constructor
    · native_decide
    constructor
    · native_decide
    constructor
    · native_decide
    · native_decide

/-- Package wrapper for the Möbius inversion localization multiset classification seeds.
    thm:cdim-multiprime-spectrum-realizability -/
theorem paper_cdim_mobius_inversion_package :
    (let S : Finset PrimeSupport := {{2}}
     multiPrimeSpectrum S ∅ = 1 ∧ multiPrimeSpectrum S {2} = 1 ∧ typeCount S {2} = 1) ∧
    (let S : Finset PrimeSupport := {{2}, {3}}
     multiPrimeSpectrum S ∅ = 2 ∧ multiPrimeSpectrum S {2} = 1 ∧
     multiPrimeSpectrum S {3} = 1 ∧ multiPrimeSpectrum S {2, 3} = 0) :=
  paper_cdim_mobius_inversion_seeds

/-- Exact-support counts recover support membership.
    thm:cdim-mobius-inversion-localization-multiset-classification -/
theorem typeCount_eq_indicator (supports : Finset PrimeSupport) (J : PrimeSupport) :
    typeCount supports J = if J ∈ supports then 1 else 0 := by
  by_cases hJ : J ∈ supports
  · have htc : typeCount supports J = 1 := by
      unfold typeCount
      have hEq : supports.filter (fun S => S = J) = {J} := by
        ext x
        constructor
        · intro hx
          simp only [Finset.mem_filter, Finset.mem_singleton] at hx ⊢
          exact hx.2
        · intro hx
          simp only [Finset.mem_filter, Finset.mem_singleton] at hx ⊢
          subst hx
          exact ⟨hJ, rfl⟩
      rw [hEq]
      simp
    simp [hJ, htc]
  · unfold typeCount
    have hEq : supports.filter (fun S => S = J) = ∅ := by
      ext x
      constructor
      · intro hx
        simp only [Finset.mem_filter] at hx
        rcases hx with ⟨hx, rfl⟩
        exact (hJ hx).elim
      · intro hx
        simp at hx
    rw [hEq]
    simp [hJ]

/-- Multiset classification from the exact-support counts. In this finite-support model the
    decomposition type is represented by the support multiset itself.
    thm:cdim-mobius-inversion-localization-multiset-classification -/
theorem paper_cdim_mobius_inversion_localization_multiset_classification
    (supports supports' : Finset PrimeSupport) :
    (∀ J : PrimeSupport,
      multiPrimeSpectrum supports J =
        Finset.sum supports (fun K => if J ⊆ K then typeCount supports K else 0)) ∧
    (∀ J : PrimeSupport, typeCount supports J = if J ∈ supports then 1 else 0) ∧
    ((∀ J : PrimeSupport, typeCount supports J = typeCount supports' J) → supports = supports') := by
  refine ⟨multiPrimeSpectrum_eq_sum_typeCount supports, typeCount_eq_indicator supports, ?_⟩
  intro hcounts
  ext J
  have hJ : typeCount supports J = typeCount supports' J := hcounts J
  rw [typeCount_eq_indicator supports J, typeCount_eq_indicator supports' J] at hJ
  by_cases hmem : J ∈ supports <;> by_cases hmem' : J ∈ supports' <;> simp [hmem, hmem'] at hJ ⊢

-- Phase R603: Inclusion-exclusion seeds
-- ══════════════════════════════════════════════════════════════

/-- Spectrum of union is bounded by min of individual spectra.
    prop:cdim-multiprime-divisible-spectrum-explicit -/
theorem multiPrimeSpectrum_union_le (supports : Finset PrimeSupport) (J K : PrimeSupport) :
    multiPrimeSpectrum supports (J ∪ K) ≤
      min (multiPrimeSpectrum supports J) (multiPrimeSpectrum supports K) :=
  Nat.le_min.mpr ⟨multiPrimeSpectrum_anti_mono Finset.subset_union_left,
                   multiPrimeSpectrum_anti_mono Finset.subset_union_right⟩

/-- Inserting a prime can only decrease the spectrum.
    prop:cdim-multiprime-divisible-spectrum-explicit -/
theorem multiPrimeSpectrum_insert_le (supports : Finset PrimeSupport) (J : PrimeSupport)
    (p : ℕ) :
    multiPrimeSpectrum supports (insert p J) ≤ multiPrimeSpectrum supports J :=
  multiPrimeSpectrum_anti_mono (Finset.subset_insert p J)

/-- Paper seeds: inclusion-exclusion at small support sets.
    prop:cdim-multiprime-divisible-spectrum-explicit -/
theorem paper_cdim_inclusion_exclusion_seeds :
    (let S : Finset PrimeSupport := {{2}, {3}, {2,3}}
     multiPrimeSpectrum S ∅ = 3 ∧
     multiPrimeSpectrum S {2} = 2 ∧
     multiPrimeSpectrum S {3} = 2 ∧
     multiPrimeSpectrum S {2,3} = 1 ∧
     typeCount S {2} = 1 ∧
     typeCount S {3} = 1 ∧
     typeCount S {2,3} = 1) := by
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide,
          by native_decide, by native_decide, by native_decide⟩

/-- Paper-facing counterexample package: two support families can have identical one-prime
    marginals and different two-prime spectrum values.
    prop:cdim-higher-spectrum-not-determined-by-marginals -/
theorem paper_cdim_higher_spectrum_not_determined_by_marginals
    {p q : Nat} (hpq : p ≠ q) :
    (∀ ℓ : Nat,
        multiPrimeSpectrum ({({p} : PrimeSupport), ({q} : PrimeSupport)} : Finset PrimeSupport)
            ({ℓ} : PrimeSupport) =
          multiPrimeSpectrum
            ({({p, q} : PrimeSupport), (∅ : PrimeSupport)} : Finset PrimeSupport)
            ({ℓ} : PrimeSupport)) ∧
      multiPrimeSpectrum ({({p} : PrimeSupport), ({q} : PrimeSupport)} : Finset PrimeSupport)
          ({p, q} : PrimeSupport) = 0 ∧
      multiPrimeSpectrum
          ({({p, q} : PrimeSupport), (∅ : PrimeSupport)} : Finset PrimeSupport)
          ({p, q} : PrimeSupport) = 1 := by
  refine ⟨?_, higher_spectrum_counterexample_pair_values (p := p) (q := q) hpq⟩
  intro ℓ
  rcases higher_spectrum_counterexample_singleton_formula
      (p := p) (q := q) (ℓ := ℓ) hpq with ⟨hA, hA'⟩
  exact hA.trans hA'.symm

end Omega.CircleDimension
